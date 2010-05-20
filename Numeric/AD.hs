{-# LANGUAGE Rank2Types, TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Numeric.AD
-- Copyright   :  (c) Edward Kmett 2010
-- License     :  BSD3
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- Portability :  GHC only 
--
-- Mixed-Mode Automatic Differentiation.
-- 
-- For reverse mode AD we use 'System.Mem.StableName.StableName' to recover sharing information from 
-- the tape to avoid combinatorial explosion, and thus run asymptotically faster
-- than it could without such sharing information, but the use of side-effects
-- contained herein is benign.
--
-----------------------------------------------------------------------------

-- TODO: Split into something like:
-- * Data.Numeric.AD.Internal
-- * Data.Numeric.AD.Tape
-- * Data.Numeric.AD.Single
-- * Data.Numeric.AD.Dual
-- * Data.Numeric.AD.Reverse
-- * Data.Numeric.AD.Newton
-- * Data.Numeric.AD.Complex
-- * Data.Numeric.AD.Matrix
-- * Data.Numeric.AD.Array
-- * Data.Numeric.AD

module Numeric.AD 
    ( D
    , Single, Tower, Dual, Reverse
    , Lifted(..)
    , Primal(..)
    , Mode(..)
    , diffUU
    , diff2UU
    , diffFU
    , diff2FU
    ) where

on :: (a -> a -> c) -> (b -> a) -> b -> b -> c
on f g a b = f (g a) (f b)

-- | A @Tape@ records the information needed back propagate from the output to each input during 'Reverse' 'Mode' AD.
data Tape a t
    = Lift a
    | Var a {-# UNPACK #-} !Int
    | Binary a a a t t
    | Unary a a t
    deriving (Show)
{-
    | Binary a a a (t a) (t a)
    | Unary a a (t a)
    | forall b. Num b => Cast a (a -> b) (b -> a) (t b)
-}

-- | @Unit@ is an AD 'Mode' that actually just ignores all input
data Unit a = Unit
-- | @Single@ is an AD 'Mode' that does no differentiation at all
newtype Single a = Single { getSingle :: a } deriving (Show)
-- | @Dual@ is an AD 'Mode' that calculates a single derivative in tangent mode, provides fast 'diffUU', 'diffUF', 'diff2UU', 'diff2UF' and 'jacobian' when you have a significantly smaller number of inputs than outputs.
newtype Dual a = Dual a a deriving (Show)
-- | @Tower@ is an AD 'Mode' that calculates a tangent tower by forward AD, provides fast 'diffsUU', 'diffsUF'
newtype Tower a = Tower { getTower :: [a] } deriving (Show)

-- | @Reverse@ is a 'Mode' using reverse-mode automatic differentiation
--
-- * @Reverse@ provides fast 'diffFU', 'diff2FU', 'grad', 'grad2' and a fast 'jacobian' when you have a significantly smaller number of outputs than inputs.
--
-- newtype Reverse a = Reverse (Tape a Reverse)
newtype Reverse a = Reverse (Tape a (Reverse a)) deriving (Show)

instance MuRef (Reverse a) where
    type DeRef (Reverse a) = Tape a
    mapDeRef f (Reverse (Lift a)) = pure (Literal a)
    mapDeRef f (Reverse (Var a v)) = pure (Var a v)
    mapDeRef f (Reverse (Binary a dadb dadc b c)) = Binary a dadb dadc <$> f b <*> f c
    mapDeRef f (Reverse (Unary a dadb b)) = Unary a dadb <$> f b


{-
-- * Applying @Reversed@ to 'Dual' provides fast 'hessian' for large numbers of control values.
-- 
-- * Applying @Reversed@ to 'Tower' provides fast 'diffsFU' for large numbers of control values.
newtype Reversed f = Reversed { getReversed :: Reverse (f a) } 

instance MuRef (Reversed f) where
    type DeRef (Reversed f a) = Tape (f a)
    mapDeRef f (Reversed xs) = mapDeRef f xs
-}

-- | Performs forward (or reverse) automatic differentiation using the specified 'Mode' @f@ using the type level brand @s@ to avoid confusing perturbations (or sensitivities).
newtype D f s a = D { runD :: f a } deriving (Show)

-- | A @Lifted@ type forms a module with a distinguished basis vector for its wrapped 'Num' instance.
class Lifted f where
    (*^)   :: Num a => a -> f a -> f a 
    (^*)   :: Num a => f a -> a -> f a 
    lift   :: Num a => a -> f a
    (<+>)  :: Num a => f a -> f a -> f a
    zero   :: Num a => f a
    one    :: Num a => f a

    zero = lift 0
    one  = lift 1
    lift a = a *^ one
    v ^* a = a *^ v

infixl 4 <+>
infixr 7 *^, \^
infixl 7 ^*, ^/

-- | Right divide a vector
(^/) :: (Lifted f, Fractional a) => f a -> a -> f a
a ^/ b = a ^* recip b

-- | Left divide a vector
(\^) :: (Lifted f, Fractional a) => a -> f a -> f a
a \^ b = recip a *^ b

instance Lifted Unit where
    lift _  = Unit
    _ <+> _ = Unit
    _ *^ _  = Unit
    _ ^* _  = Unit
    zero    = Unit
    one     = Unit

instance Lifted Single where
    Single a <+> Single b = Single (a + b) 

    lift = Single

    a *^ Single b = Single (a * b)

    Single a ^* b = Single (a * b)
   
instance Lifted Tower where
    lift a = Tower [a]

    zero = Tower []

    Tower [] <+> bs = bs
    as <+> Tower [] = as
    Tower (a:as) <+> Tower (b:bs) = Tower (c:cs)
        where c = a + b
            Tower cs = Tower as <+> Tower bs

    a *^ Tower bs = Tower (map (a*) bs)

    Tower as ^* b = Tower (map (*b) as)

instance Lifted Dual where
    lift a = Dual a 0

    Dual a b <+> Dual c d = Dual (a + c) (b + d)

    a *^ Dual b b' = Dual (a * b) (a * b')

    Dual a a' ^* b = Dual (a * b) (a' * b)

instance Lifted Reverse where
    lift a = Reverse (Lift a)

    Reverse (Lift a) <+> Reverse (Lift b) = lift (a + b)
    a <+> Reverse (Lift pb) = Reverse (Unary (primal a + pb) one a)
    Reverse (Lift pa) <+> b = Reverse (Unary (pa + primal b) one b)

    pa *^ Reverse (Lift pb) = Reverse (Lift (pa*pb))
    pa *^ b = Reverse (Unary (pa * primal b) pa b)

    Reverse (Lift pa) ^* pb = Reverse (Lift (pa*pb))
    a ^* pb = Reverse (Unary (primal a * pb) pb a)

{-
instance Lifts a a where
  lifts a = a

instance (TypeCast (D s b') b, Num b', Lifts a b')
  => Lifts a b where
  lifts = typeCast . lift . lifts

class TypeCast a b | a -> b, b -> a where
  typeCast :: a -> b
class TypeCast' t a b | t a -> b, t b -> a where
  typeCast' :: t -> a -> b
class TypeCast'' t a b | t a -> b, t b -> a where
  typeCast'' :: t -> a -> b
instance TypeCast' () a b => TypeCast a b where
  typeCast x = typeCast' () x
instance TypeCast'' t a b => TypeCast' t a b where
  typeCast' = typeCast''
instance TypeCast'' () a a where
  typeCast'' _ x  = x
-}

{-
instance Lifted f => Lifted (Reversed f) where
    lift a = Reversed (lift (lift a))

    Reverse (Lift a) <+> Reverse (Lift b) = lift (a <+> b)
    a <+> Reverse (Lift pb) = Reverse (Unary (primal a <+> pb) one a)
    Reverse (Lift pa) <+> b = Reverse (Unary (pa <+< primal b) one b)

    a *^ Reverse (Lift pb) = Reverse (Lift (a*^ pb))
    a *^ b = Reverse (Unary (a *^ primal b) pa b)

    Reverse (Lift pa) ^* b = Reverse (Lift (pa ^* b))
    a ^* b = Reverse (Unary (primal a ^* b) pb a)
-}

instance Lifted f => Lifted (D f s) where
    {-# SPECIALIZE instance Lifted (D Reverse s) #-}
    {-# SPECIALIZE instance Lifted (D Single s) #-}
    {-# SPECIALIZE instance Lifted (D Tower s) #-}
    {-# SPECIALIZE instance Lifted (D Dual s) #-}
    {-# SPECIALIZE instance Lifted (D Unit s) #-}

    lift a = D (lift a)

    a <+> b = D (a <+> b)

    a *^ D bs = D (a *^ bs)

    D as ^* b = D (as ^* b)
    
-- | length of the projection onto the distinguished basis vector provided by 'Lifted'
class Lifted f => Primal f where
    primal :: f a -> a

instance Primal Single where    
    primal (Single a) = a

instance Primal Tower where
    primal (Tower x _) = x

instance Primal Dual where
    primal (Dual a _) = a

instance Primal Reverse where
    primal (Reverse (Lift a)) = a
    primal (Reverse (Var a _)) = a
    primal (Reverse (Binary a _ _ _ _)) = a
    primal (Reverse (Unary a _ _) = a
--  primal (Reverse (Cast a _ _ _)) = a

{-
-- this is somewhat problematic, since ideally the operations in Reversed should be lifted. as well.
instance Primal f => Primal (Reversed f) where
    primal (Reversed xs) = primal (primal xs)
-}

instance Primal f => Primal (D f s) where
    {-# SPECIALIZE instance Primal (D Reverse s) #-}
    {-# SPECIALIZE instance Primal (D Single s) #-}
    {-# SPECIALIZE instance Primal (D Tower s) #-}
    {-# SPECIALIZE instance Primal (D Dual s) #-}
    primal (D a) = primal a

-- | Minimum definition: 'lift2_' and 'lift1_'
class (Primal t, Lifted (Jacobian t)) => Mode t where
    type Jacobian t :: * -> *

    unary   :: a -> Jacobian t a -> t a -> t a
    lift1   :: (a -> a) -> (Jacobian t a -> Jacobian t a) -> t a -> t a
    lift1_  :: (a -> a) -> (Jacobian t a -> Jacobian t a -> Jacobian t a) -> t a -> t a

    binary :: a -> Jacobian t a -> Jacobian t a -> t a -> t a -> t a
    lift2  :: (a -> a -> a) -> (Jacobian t a -> Jacobian t a -> (Jacobian t a, Jacobian t a)) -> t a -> t a -> t a
    lift2_ :: (a -> a -> a) -> (Jacobian t a -> Jacobian t a -> Jacobian t a -> (Jacobian t a, Jacobian t a)) -> t a -> t a -> t a 

    unary a dadb = lift1 (const a) (const dadb)
    lift1 f g = lift1_ f (const g)
    
    binary a dadb dadc = lift2 (\_ _ -> a) (\_ _ -> (dadb, dadc))
    lift2 f g = lift2_ f (const g)

    
instance Mode Single where
    type Jacobian Single = Unit

    unary a _ _ = Single a
    lift1 f _ (Single b) = Single (f b)
    lift1_ f _ (Single b) = Single (f b)

    binary a _ _ _ _ = Single a
    lift2 f _ (Single b) (Single c) = Single (f b c)
    lift2_ f _ (Single b) (Single c) = Single (f b c)

tangent :: Dual a b -> Single b
tangent (Dual a b) = Single b

instance Mode Dual where
    type Jacobian Dual = Single

    unary a (Single dadb) (Dual _ db) = Dual a (dadb * db)

    lift1 f df (Dual b db) = Dual (f b) (dadb * db)
        where Single dadb = df (Single b)

    lift1_ f df (Dual b db) = Dual a da
        where a = f b
              Single da = df (Single a) (Single b) ^* db

    binary a (Single dadb) (Single dadc) (Dual _ db) (Dual _ dc) = Dual a da
        where da = dadb * db + dc * dadc

    lift2 f df (Dual b db) (Dual c dc) = Dual a da
        where (Single dadb, Single dadc) = df (Single b) (Single c) 
              da = dadb * db + dc * dadc

    lift2_ f df (Dual b db) (Dual c dc) = Dual a da
        where a = f b c
              (Single dadb, Single dadc) = df (Single a) (Single b) (Single c)
              da = dadb * db + dc * dadc

-- | extract the tangent tower from a tangent bundle
tangents :: Tower a -> Tower a
tangents (Tower []) = Tower []
tangents (Tower (x:xs)) = Tower xs)

-- | bundle a point with tangent vector tower at that point
bundle :: a -> Tower a -> Tower a
bundle a (Tower as) = Tower (a:as)

instance Mode Tower where
    type Jacobian Tower = Tower

    unary a dadb b = bundle a (tangents b * dadb)

    lift1 f df b = bundle (f (primal b)) (tangents b * df b)

    lift1_ f df b = a where 
        a = bundle (f (primal b)) (tangents b * df a b)

    binary a dadb dadc b c = bundle a (tangents b * dadb + tangents c * dadc) 

    lift2 f df b c = bundle (f (primal b) (primal c)) (tangents b * dadb + tangents c * dadc) where
        (dadb, dadc) = df b c 

    lift2_ f df b c = a where 
        a = bundle (f (primal b) (primal c)) (tangents b * dadb + tangents c * dadc)
        (dadb, dadc) = df a b c
       

instance Mode Reverse where
    type Jacobian Reverse = Single

    unary a _ (Reverse Constant{}) = Reverse (Constant a)
    unary a (Single dadb) b = Reverse (Unary a dadb b))

    lift1 f df b = unary (f pb) (df (Single pb)) b 
        where pb = primal b

    lift1_ f df b = unary a (df (Single a) (Single pb)) b 
        where pb = primal b
              a = f pb

    binary a _            _              (Reverse Constant {}) (Reverse Constant {}) = Reverse (Constant a)
    binary a _            (Single dadc)  (Reverse Constant {}) c                     = Reverse (Unary a dadc c)
    binary a (Single dadb) _             b                     (Reverse Constant{})  = Reverse (Unary a dadb b)
    binary a (Single dadb) (Single dadc) b                     c                     = Reverse (Binary a dadb dadc b c)

    lift2 f df b c = binary a dadb dadc b c
        where 
            pb = primal b
            pc = primal c 
            a = f pb pc
            (Single dadb, Single dadc) = df (Single pb) (Single pc)

    lift2_ f df b c = binary a dadb dadc b c
        where 
            pb = primal b
            pc = primal c
            a = f pb pc
            (Single dadb, Single dadc) = df (Single a) (Single pb) (Single pc)

-- instance Mode t => Mode (Reversed t) where
--    type Jacobian (Reversed t) = t
    

ad1 :: (D f s a -> D f s a) -> f a -> f a
ad1 f a = getD (f (D a))

ad1_ :: (D f s a -> D f s a -> D f s a) -> f a -> f a -> f a
ad1_ f a = getD (f (D a))

ad2 :: (D f s a -> D f s a -> (D f s a, D f s a)) -> f a -> f a -> (f a, f a)
ad2 f b c = (adb,adc)
    (D adb, D adc) = f (D b) (D c)

ad2_ :: (D f s a -> D f s a -> D f s a -> (D f s a, D f s a)) -> f a -> f a -> f a -> (f a, f a)
ad2_ f a b c = (adb,adc)
    (D adb, D adc) = f (D a) (D b) (D c)

instance Mode t => Mode (D t s) where
    type Jacobian (D t s) = D (Jacobian t) s
    unary a (D dadb) (D b) = D (unary a dadb b)
    binary a (D dadb) (D dadc) (D b) (D c) = D (binary a dadb dadc b c)
    lift1 f g (D b) = D (lift1 f (ad1 g) b)
    lift1_ f g (D b) = D (lift1_ f (ad1_ g) b)
    lift2 f g (D b) (D c) = D (lift2 f (ad2 g) b c)
    lift2_ f g (D b) (D c) = D (lift2_ f (ad2_ g) b c)

discrete1 :: Primal f => (a -> b) -> f a -> b
discrete1 f x = f (primal x)
{-# INLINE discrete1 #-}

discrete2 :: Primal f => (a -> b -> c) -> f a -> f b -> c
discrete2 f x y = f (primal x) (primal y)
{-# INLINE discrete2 #-}

discrete3 :: Primal f => (a -> b -> c -> d) -> f a -> f b -> f c -> d
discrete3 f x y z = f (primal x) (primal y) (primal z)
{-# INLINE discrete3 #-}

{- -- expects that the a -> b, and b -> a arguments form an approximate ring-isomorphism
class Cast t where
    castWith :: (a -> b) -> (b -> a) -> t a -> t b

instance Cast t => Cast (D f s) where
    castWith f g (D a) = D (castWith f g a)

fromD :: (Cast f, Floating a, Floating b) => f a -> f b 
fromD = castWith (fromRational . toRational) (fromRational . toRational)
-}

-- instance (Primal t, Show a) => Show (D t s a) where
--    showsPrec (D t) = showsPrec d `on` primal

instance (Primal t, Eq a) => Eq (D t s a) where
    (==) = (==) `on` primal

instance (Primal t, Ord a) => Ord (D t s a) where
    compare = compare `on` primal

instance (Lifted t, Bounded a) => Bounded (D t s a) where
    maxBound = lift maxBound
    minBound = lift minBound

instance (Num a, Mode t, Num (Jacobian t a)) => Num (D t s a) where
    fromInteger n = lift (fromInteger n)
    (+)    = (<+>)
    (-)    = lift2 (-) (\_ _ -> (1,-1))
    (*)    = lift2 (*) (\b c -> (c, b))
    negate = negate >-< const (-1)
    abs    = abs >-< signum
    signum = lift . signum . primal

(>-<) :: Mode t => (a -> a) -> (Jacobian t a -> Jacobian t a) -> t a -> t a
(>-<) = lift1
{-# INLINE (>-<) #-}

square :: Num a => a -> a
square x = x * x 

instance (Floating a, Mode t, Num (Jacobian t a)) => Floating (D t s a) where
    pi      = lift pi
    exp     = lift1_ exp const
    sqrt    = lift1_ sqrt (\z _ -> recip (2 * z))
    -- TODO: 0**n
    (**)    = lift2_ (**) (\z x y -> (y*z/x, z*log x))
    log     = log   >-< recip 
    sin     = sin   >-< cos
    cos     = cos   >-< \x -> negate (sin x)
    asin    = asin  >-< \x -> recip (sqrt (1 - square x))
    acos    = acos  >-< \x -> negate (recip (sqrt (1 - square x))
    atan    = atan  >-< \x -> recip (1 + square x)
    sinh    = sinh  >-< cosh
    cosh    = cosh  >-< sinh
    asinh   = asinh >-< \x -> recip (sqrt (1 + square x))
    acosh   = acosh >-< \x -> recip (sqrt (square x - 1))
    atanh   = atanh >-< \x -> recip (1 - square x)

class Var f where
    var :: a -> Int -> f a

instance Var (Reverse f) where
    var a v = Reverse (Var a v)

-- instance Var f => Var (Reversed f) where
--    var a v = Reversed (var a v)

instance Var f => Var (D f s) where
    var a v = D (var a v)

d :: Dual a -> a
d (Dual _ a) = a

-- | The 'diffUU' function calculates the first derivative of a scalar-to-scalar function by forward AD
diffUU :: Num a => (forall s. D Dual s a -> D Dual s a) -> a -> a
diffUU f a = d $ f (Dual a 1)

-- | The 'diffUF' function calculates the first derivative of scalar-to-nonscalar function by forward AD
diff2UU :: Num a => (forall s. D Dual s a -> D Dual s a) -> a -> (a, a) 
diff2UU f a = runDual $ f (Dual a 1)

-- | The 'diffUF' function calculates the first derivative of scalar-to-nonscalar function by forward AD
diffUF :: (Functor f, Num a) => (forall s. D Dual s a -> f (D Dual s a)) -> a -> f a
diffUF f a = d <$> f (Dual a 1)

diff2UF :: (Functor f, Num a) => (forall s. D Dual s a -> f (D Dual s a)) -> a -> f (a, a) 
diff2UF f a = runDual <$> f (Dual a 1)

-- | THe 'grad' function calculates the gradient of a non-scalar-to-scalar function with 'Reverse' AD
grad       :: (Num a, Traversable f) => 
              (forall s. f (D Reverse s a) -> D Reverse s a) -> 
              f a -> f a

-- | THe 'grad' function calculates the gradient of a non-scalar-to-scalar function with 'Reverse' AD
grad2      :: (Num a, Traversable f) => 
              (forall s. f (D Reverse s a) -> D Reverse s a) -> 
              f a -> (b, f a)

fjacobian  :: (Num a, Traversable f, Functor g) => 
              (forall s. f (D Dual s a) -> g (D Dual s a)) -> 
              f a -> g (f a)

fjacobian2 :: (Num a, Traversable f, Functor g) => 
              (forall s. f (D Dual s a) -> g (D Dual s a)) -> 
              f a -> g (a, f a)

jacobian   :: (Num b, Traversable f, Functor g) => 
              (forall s. f (D Reverse s a) -> g (D Reverse s b)) -> 
              f a -> g (f a)

jacobian2  :: (Num b, Traversable f, Functor g) => 
              (forall s. f (D Reverse s a) -> g (D Reverse s b)) -> 
              f a -> g (b, f a)

hessianU  :: (Num b, Traversable f) => 
              (forall s t. f (D Reverse s (D Dual t a)) -> D (Reverse s (D Dual t a))) -> 
              f a -> f (f a))

hessianF  :: (NUm b, Traversable f, Functor g) => 
              (forall s t. f (D Reverse s (D Dual t a)) -> g (D (Reverse s (D Dual t a)))) ->
              f a -> g (f (f a))

hessian3U :: (Num b, Traversable f) => 
              (forall s t. f (D Reverse s (D Dual t a)) -> D (Reverse s (D Dual t a))) ->
              f a -> (a, f (a, f a))

hessian3F :: (Num b, Traversable f, Functor g) => 
              (forall s t. f (D Reverse s (D Dual t a)) -> g (D (Reverse s (D Dual t a)))) -> 
              f a -> g (a, f (a, f a))

diffFU :: (Num a => f (D Reverse s a) -> 

-- reverse -| forward
class Adjoint f g | f -> g, g -> f where
    checkUU :: (forall s. D g s a -> D g s b) -> D f t a -> D f t a
    checkUF :: Functor m => (forall s. D g s a -> m (D g s a)) -> D f t a -> m (D f t a)
    checkFU :: Traversable n => (forall s. n (D f s a) -> D f s a) -> n (D g t a) -> D g t a
    checkRFF :: (Traversable n, Functor m) => (forall s. n (D f s a) -> m (D f s a)) -> n (D g t a) -> m (D g t a)
    checkTFF :: (Traversable n, Functor m) => (forall s. n (D g s a) -> m (D g s a)) -> n (D f t a) -> m (D f t a)

instance Adjoint Single Single where

instance Adjoint (Reverse Single) Dual where

instance Adjoint (Reverse Tower) Tower where


module Numeric.RAD 
    ( 
    -- * First-Order Reverse Mode Automatic Differentiation
      RAD
    , lift
    -- * First-Order Differentiation Operators
    , diffUU
    , diffUF
    , diff2UU
    , diff2UF
    -- * Common access patterns 
    , diff
    , diff2
    , jacobian
    , jacobian2
    , grad
    , grad2
    -- * Optimization Routines 
    , zeroNewton
    , inverseNewton
    , fixedPointNewton
    , extremumNewton
    , argminNaiveGradient
    ) where

import Prelude hiding (mapM)
import Control.Applicative (Applicative(..),(<$>))
import Control.Monad.ST
import Control.Monad (forM_)
import Data.List (foldl')
import Data.Array.ST
import Data.Array
import Data.Ix
import Text.Show
import Data.Graph (graphFromEdges', topSort, Vertex)
import Data.Reify (reifyGraph, MuRef(..))
import qualified Data.Reify.Graph as Reified
import Data.Traversable (Traversable, mapM)
import System.IO.Unsafe (unsafePerformIO)

from :: Num a => RAD s a -> a -> RAD s a
from (RAD (Literal a)) x = RAD (Literal x)
from a x = RAD (Unary x 1 a)

fromBy :: Num a => RAD s a -> RAD s a -> Int -> a -> RAD s a 
fromBy (RAD (Literal a)) _ _ x = RAD (Literal x)
fromBy a delta n x = RAD (Binary x 1 (fromIntegral n) a delta)

instance (Num a, Enum a) => Enum (RAD s a) where
    succ = lift1_ succ 1
    pred = lift1_ pred 1
    toEnum   = lift . toEnum
    fromEnum = discrete1 fromEnum
    -- the enumerated results vary with the lower bound and so their derivatives reflect that
    enumFrom a           = from a <$> discrete1 enumFrom a
    enumFromTo a b       = from a <$> discrete2 enumFromTo a b
    -- these results vary with respect to both the lower bound and the delta between that and the second argument
    enumFromThen a b     = zipWith (fromBy a delta) [0..] $ discrete2 enumFromThen a b where delta = b - a
    enumFromThenTo a b c = zipWith (fromBy a delta) [0..] $ discrete3 enumFromThenTo a b c where delta = b - a

instance Num a => Num (RAD s a) where
    fromInteger = lift . fromInteger
    (+) = lift2_ (+) 1 1 
    (-) = lift2_ (-) 1 (-1)
    negate = lift1_ negate (-1)
    (*) = lift2 (*) id id
    -- incorrect if the argument is complex
    abs = lift1 abs signum
    signum = lift . signum . primal

-- notComplex :: Num a => a -> Bool
-- notComplex x = s == 0 || s == 1 || s == -1
--     where s = signum x 

instance Real a => Real (RAD s a) where
    toRational = discrete1 toRational

instance RealFloat a => RealFloat (RAD s a) where
    floatRadix = discrete1 floatRadix
    floatDigits = discrete1 floatDigits
    floatRange = discrete1 floatRange

    decodeFloat = discrete1 decodeFloat
    encodeFloat m e = lift (encodeFloat m e)

    scaleFloat n = lift1_ (scaleFloat n) (scaleFloat n 1) 
    isNaN = discrete1 isNaN
    isInfinite = discrete1 isInfinite
    isDenormalized = discrete1 isDenormalized
    isNegativeZero = discrete1 isNegativeZero
    isIEEE = discrete1 isIEEE

    exponent x
        | m == 0 = 0 
        | otherwise = n + floatDigits x
        where (m,n) = decodeFloat x 

    significand x =  lift1_ significand (scaleFloat (- floatDigits x) 1) x

    atan2 (RAD (Literal x)) (RAD (Literal y)) = RAD (Literal (atan2 x y))
    atan2 x y = RAD (Binary (atan2 vx vy) (vy*r) (-vx*r) x y)
        where vx = primal x
              vy = primal y
              r = recip (vx^2 + vy^2)

instance RealFrac a => RealFrac (RAD s a) where
    properFraction (RAD (Literal a)) = (w, RAD (Literal p))
        where (w, p) = properFraction a
    properFraction a = (w, RAD (Unary p 1 a))
        where (w, p) = properFraction (primal a)
    truncate = discrete1 truncate
    round = discrete1 truncate
    ceiling = discrete1 truncate
    floor = discrete1 truncate

instance Fractional a => Fractional (RAD s a) where
    (/) = lift2 (/) recip id
--   recip = lift1 recip  (const . negate . (^2))
    fromRational r = lift $ fromRational r

instance Floating a => Floating (RAD s a) where
    pi      = lift pi
    exp     = lift1 exp exp
    log     = lift1 log recip
    sqrt    = lift1 sqrt (recip . (2*) . sqrt)
    RAD (Literal x) ** RAD (Literal y) = lift (x ** y)
    x ** y  = RAD (Binary vz (vy*vz/vx) (vz*log vx) x y)
        where vx = primal x
              vy = primal y
              vz = vx ** vy
    sin     = lift1 sin cos
    cos     = lift1 cos (negate . sin)
    asin    = lift1 asin (recip . sqrt . (1-) . (^2))
    acos    = lift1 acos (negate . recip . sqrt . (1-) . (^2))
    atan    = lift1 atan (recip . (1+) . (^2))
    sinh    = lift1 sinh cosh
    cosh    = lift1 cosh sinh
    asinh   = lift1 asinh (recip . sqrt . (1+) . (^2))
    acosh   = lift1 acosh (recip . sqrt . (-1+) . (^2))
    atanh   = lift1 atanh (recip . (1-) . (^2))

-- back propagate sensitivities along the tape.
backprop :: (Ix t, Ord t, Num a) => (Vertex -> (Tape a t, t, [t])) -> STArray s t a -> Vertex -> ST s ()
backprop vmap ss v = do
        case node of
            Unary _ g b -> do
                da <- readArray ss i
                db <- readArray ss b
                writeArray ss b (db + g*da)
            Binary _ gb gc b c -> do
                da <- readArray ss i
                db <- readArray ss b
                writeArray ss b (db + gb*da)
                dc <- readArray ss c
                writeArray ss c (dc + gc*da)
            _ -> return ()
    where 
        (node, i, _) = vmap v

runTape :: Num a => (Int, Int) -> RAD s a -> Array Int a 
runTape vbounds tape = accumArray (+) 0 vbounds [ (id, sensitivities ! ix) | (ix, Var _ id) <- xs ]
    where
        Reified.Graph xs start = unsafePerformIO $ reifyGraph tape
        (g, vmap) = graphFromEdges' (edgeSet <$> filter nonConst xs)
        sensitivities = runSTArray $ do
            ss <- newArray (sbounds xs) 0
            writeArray ss start 1
            forM_ (topSort g) $ 
                backprop vmap ss
            return ss
        sbounds ((a,_):as) = foldl' (\(lo,hi) (b,_) -> (min lo b, max hi b)) (a,a) as
        edgeSet (i, t) = (t, i, successors t)
        nonConst (_, C{}) = False
        nonConst _ = True
        successors (Unary _ _ b) = [b]
        successors (Binary _ _ _ b c) = [b,c]
        successors _ = []    

        -- this isn't _quite_ right, as it should allow negative zeros to multiply through
        -- but then we have to know what an isNegativeZero looks like, and that rather limits
        -- our underlying data types we can permit.
        -- this approach however, allows for the occasional cycles to be resolved in the 
        -- dependency graph by breaking the cycle on 0 edges.

        -- test x = y where y = y * 0 + x

        -- successors (Unary _ db b) = edge db b []
        -- successors (Binary _ db dc b c) = edge db b (edge dc c [])
        -- successors _ = []    

        -- edge 0 x xs = xs
        -- edge _ x xs = x : xs

d :: Num a => RAD s a -> a
d r = runTape (0,0) r ! 0 

d2 :: Num a => RAD s a -> (a,a)
d2 r = (primal r, d r)


-- diffMU :: Num a => (forall s. [RAD s a] -> RAD s a) -> [a] -> [a] -> a
-- TODO: finish up diffMU and their ilk

-- avoid dependency on MTL
newtype S a = S { runS :: Int -> (a,Int) } 

instance Monad S where
    return a = S (\s -> (a,s))
    S g >>= f = S (\s -> let (a,s') = g s in runS (f a) s')
    
bind :: Traversable f => f a -> (f (RAD s a), (Int,Int))
bind xs = (r,(0,s)) 
    where 
        (r,s) = runS (mapM freshVar xs) 0
        freshVar a = S (\s -> let s' = s + 1 in s' `seq` (RAD (Var a s), s'))

unbind :: Functor f => f (RAD s b) -> Array Int a -> f a 
unbind xs ys = fmap (\(RAD (Var _ i)) -> ys ! i) xs

-- | The 'diff2UU' function calculates the value and derivative, as a
-- pair, of a scalar-to-scalar function.
diff2UU :: Num a => (forall s. RAD s a -> RAD s a) -> a -> (a, a)
diff2UU f a = d2 $ f (var a 0)

-- | Note that the signature differs from that used in Numeric.FAD, because while you can always
-- 'unzip' an arbitrary functor, not all functors can be zipped.
diff2UF :: (Functor f, Num a) => (forall s. RAD s a -> f (RAD s a)) -> a -> f (a, a)
diff2UF f a = d2 <$> f (var a 0)

-- | The 'diff' function is a synonym for 'diffUU'.
diff :: Num a => (forall s. RAD s a -> RAD s a) -> a -> a
diff = diffUU 

-- | The 'diff2' function is a synonym for 'diff2UU'.
diff2 :: Num a => (forall s. RAD s a -> RAD s a) -> a -> (a, a)
diff2 = diff2UU

-- requires the input list to be finite in length
grad :: (Traversable f, Num a) => (forall s. f (RAD s a) -> RAD s a) -> f a -> f a
grad f as = unbind s (runTape bounds $ f s)
    where (s,bounds) = bind as

-- compute the primal and gradient
grad2 :: (Traversable f, Num a) => (forall s. f (RAD s a) -> RAD s a) -> f a -> (a, f a)
grad2 f as = (primal r, unbind s (runTape bounds r))
    where (s,bounds) = bind as
          r = f s

-- | The 'jacobian' function calcualtes the Jacobian of a
-- nonscalar-to-nonscalar function, using m invocations of reverse AD,
-- where m is the output dimensionality. When the output dimensionality is
-- significantly greater than the input dimensionality you should use 'Numeric.FAD.jacobian' instead.
jacobian :: (Traversable f, Functor g, Num a) => (forall s. f (RAD s a) -> g (RAD s a)) -> f a -> g (f a)
jacobian f as = unbind s . runTape bounds <$> f s
    where (s, bounds) = bind as

-- | The 'jacobian2' function calcualtes both the result and the Jacobian of a
-- nonscalar-to-nonscalar function, using m invocations of reverse AD,
-- where m is the output dimensionality. 
-- 'fmap snd' on the result will recover the result of 'jacobian'
jacobian2 :: (Traversable f, Functor g, Num a) => (forall s. f (RAD s a) -> g (RAD s a)) -> f a -> g (a, f a)
jacobian2 f as = row <$> f s
    where (s, bounds) = bind as
          row a = (primal a, unbind s (runTape bounds a))

-- | The 'zeroNewton' function finds a zero of a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--  @take 10 $ zeroNewton (\\x->x^2-4) 1  -- converge to 2.0@
--
-- TEST CASE
--  :module Data.Complex Numeric.RAD
--  @take 10 $ zeroNewton ((+1).(^2)) (1 :+ 1)  -- converge to (0 :+ 1)@
--
zeroNewton :: Fractional a => (forall s. RAD s a -> RAD s a) -> a -> [a]
zeroNewton f x0 = iterate (\x -> let (y,y') = diff2UU f x in x - y/y') x0

-- | The 'inverseNewton' function inverts a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--   @take 10 $ inverseNewton sqrt 1 (sqrt 10)  -- converge to 10@
--
inverseNewton :: Fractional a => (forall s. RAD s a -> RAD s a) -> a -> a -> [a]
inverseNewton f x0 y = zeroNewton (\x -> f x - lift y) x0

-- | The 'fixedPointNewton' function find a fixedpoint of a scalar
-- function using Newton's method; its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)
fixedPointNewton :: Fractional a => (forall s. RAD s a -> RAD s a) -> a -> [a]
fixedPointNewton f = zeroNewton (\x -> f x - x)

-- | The 'extremumNewton' function finds an extremum of a scalar
-- function using Newton's method; produces a stream of increasingly
-- accurate results.  (Modulo the usual caveats.)
extremumNewton :: Fractional a => (forall s t. RAD t (RAD s a) -> RAD t (RAD s a)) -> a -> [a]
extremumNewton f x0 = zeroNewton (diffUU f) x0

-- | The 'argminNaiveGradient' function performs a multivariate
-- optimization, based on the naive-gradient-descent in the file
-- @stalingrad\/examples\/flow-tests\/pre-saddle-1a.vlad@ from the
-- VLAD compiler Stalingrad sources.  Its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)  
-- This is /O(n)/ faster than 'Numeric.FAD.argminNaiveGradient'
argminNaiveGradient :: (Fractional a, Ord a) => (forall s. [RAD s a] -> RAD s a) -> [a] -> [[a]]
argminNaiveGradient f x0 =
    let
        gf = grad f
        loop x fx gx eta i =
            -- should check gx = 0 here
            let
                x1 = zipWith (+) x (map ((-eta)*) gx)
                fx1 = lowerFU f x1
                gx1 = gf x1
            in
              if eta == 0 then []
              else if (fx1 > fx) then loop x fx gx (eta/2) 0
                   else if all (==0) gx then []
                        -- else if fx1 == fx then loop x1 fx1 gx1 eta (i+1)
                        else x1:(if (i==10)
                                 then loop x1 fx1 gx1 (eta*2) 0
                                 else loop x1 fx1 gx1 eta (i+1))
    in
      loop x0 (lowerFUnary f x0) (gf x0) 0.1 0

{-
lowerUU :: (forall s. RAD s a -> RAD s b) -> a -> b
lowerUU f = primal . f . lift

lowerUF :: Functor f => (forall s. RAD s a -> f (RAD s b)) -> a -> f b
lowerUF f = fmap primal . f . lift

lowerFF :: (Functor f, Functor g) => (forall s. f (RAD s a) -> g (RAD s b)) -> f a -> g b
lowerFF f = fmap primal . f . fmap lift
-}

lowerFU :: Functor f => (forall s. f (RAD s a) -> RAD s b) -> f a -> b
lowerFU f = primal . f . fmap lift
-}
