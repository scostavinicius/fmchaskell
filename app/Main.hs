{-# LANGUAGE NoImplicitPrelude #-}

module Main where

import Prelude (Bool (..), IO, error, otherwise, putStrLn, (&&), (||))

-- ----------------------------------
-- Tipos de dados
-- ----------------------------------
data Nat = O | S Nat

data List a = Nil | Cons a (List a)

data Unit = Unit

data Empty

data Maybe a = Nothing | Just a

data Either a b = L a | R b

-- ----------------------------------
-- Funções dos Nats
-- ----------------------------------
(+) :: Nat -> Nat -> Nat
n + O = n
O + m = m
S n + S m = S (n + m)

(*) :: Nat -> Nat -> Nat
_ * O = O
O * _ = O
n * S m = (n * m) + S n

(^) :: Nat -> Nat -> Nat
_ ^ O = S O
n ^ S m = (n ^ m) * n

(<) :: Nat -> Nat -> Bool
(S n) < (S m) = n < m
O < (S _) = True
_ < _ = False

(>) :: Nat -> Nat -> Bool
(S n) > (S m) = n > m
(S _) > O = True
_ > _ = False

sub :: Nat -> Nat -> Nat
sub O _ = O
sub n O = n
sub (S n) (S m) = sub n m

double :: Nat -> Nat
double O = O
double (S n) = S (S (double n))

-- Menor ou igual e Igual
leq :: Nat -> Nat -> Bool
leq O _ = Prelude.True
leq (S n) (S m) = leq n m
leq _ _ = False

eq :: Nat -> Nat -> Bool
eq O O = True
eq (S n) (S m) = eq n m
eq _ _ = False

-- Par e Impar
even :: Nat -> Bool
even O = True
even (S n) = odd n

odd :: Nat -> Bool
odd O = False
odd (S n) = even n

-- Fatorial e Fibonacci
fact :: Nat -> Nat
fact O = S O
fact (S n) = (S n) * fact n

fib :: Nat -> Nat
fib O = S O
fib (S O) = S O
fib (S (S n)) = fib n + fib (S n)

-- Mínimo e Máximo
min :: Nat -> Nat -> Nat
min (S n) (S m) = S (min n m)
min _ _ = O

max :: Nat -> Nat -> Nat
max (S n) (S m) = S (max n m)
max n O = n
max O m = m

-- Funções para a divisão
quot :: Nat -> Nat -> Nat
quot n m
  | leq n m = O
  | otherwise = S (quot (sub n m) m)

rem :: Nat -> Nat -> Nat
rem n m
  | leq n m = n
  | otherwise = rem (sub n m) m

div :: Nat -> Nat -> (Nat, Nat)
div n m = (quot n m, rem n m)

-- ----------------------------------
-- Funções de List Nat
-- ----------------------------------
sum :: List Nat -> Nat
sum Nil = O
sum (Cons n ns) = n + sum ns

prod :: List Nat -> Nat
prod Nil = S O
prod (Cons n ns) = n * prod ns

doubles :: List Nat -> List Nat -- Subst. por map double
doubles Nil = Nil
doubles (Cons n ns) = Cons (double n) (doubles ns)

-- pointwise e sua abstração
pwAdd :: List Nat -> List Nat -> List Nat
pwAdd (Cons n ns) (Cons m ms) = Cons (n + m) (pwAdd ns ms)
pwAdd _ _ = Nil

pwMult :: List Nat -> List Nat -> List Nat
pwMult (Cons n ns) (Cons m ms) = Cons (n * m) (pwMult ns ms)
pwMult _ _ = Nil

pw :: (Nat -> Nat -> Nat) -> List Nat -> List Nat -> List Nat
pw op (Cons n ns) (Cons m ms) = Cons (op n m) (pw op ns ms)
pw _ _ _ = Nil

-- allEven, anyEven e allOdd, anyOdd
allEven :: List Nat -> Bool
allEven (Cons n ns) = even n && allEven ns
allEven Nil = True

anyEven :: List Nat -> Bool
anyEven (Cons n ns) = even n || anyEven ns
anyEven Nil = False

allOdd :: List Nat -> Bool
allOdd (Cons n ns) = odd n && allOdd ns
allOdd Nil = True

anyOdd :: List Nat -> Bool
anyOdd (Cons n ns) = odd n || anyOdd ns
anyOdd Nil = False

allZero :: List Nat -> Bool
allZero (Cons n ns) = eq n O && allZero ns
allZero Nil = True

anyZero :: List Nat -> Bool
anyZero (Cons n ns) = eq n O || anyZero ns
anyZero Nil = False

-- operações em listas
addNat :: Nat -> List Nat -> List Nat
addNat n (Cons m ms) = Cons (m + n) (addNat n ms)
addNat _ Nil = Nil

multNat :: Nat -> List Nat -> List Nat
multNat n (Cons m ms) = Cons (m * n) (multNat n ms)
multNat _ Nil = Nil

expNat :: Nat -> List Nat -> List Nat
expNat n (Cons m ms) = Cons (m ^ n) (expNat n ms)
expNat _ Nil = Nil

-- enum
enumFromTo :: Nat -> Nat -> List Nat
enumFromTo n m
  | n > m = Nil
  | otherwise = Cons n (enumFromTo (S n) m)

enumTo :: Nat -> List Nat
enumTo n = enumFromTo O n

-- ordenação
isSorted :: List Nat -> Bool
isSorted Nil = True
isSorted (Cons _ Nil) = True
isSorted (Cons n (Cons n' ns)) = leq n n' && isSorted (Cons n' ns)

-- filters
filterEven :: List Nat -> List Nat
filterEven Nil = Nil
filterEven (Cons n ns)
  | even n = Cons n (filterEven ns)
  | otherwise = filterEven ns

filterOdd :: List Nat -> List Nat
filterOdd Nil = Nil
filterOdd (Cons n ns)
  | odd n = Cons n (filterEven ns)
  | otherwise = filterOdd ns

-- minimo e maximo
minimum :: List Nat -> Nat
minimum Nil = error "Empty list: no minimum value"
minimum (Cons n Nil) = n
minimum (Cons n (Cons n' ns))
  | n < n' = minimum (Cons n ns)
  | otherwise = minimum (Cons n' ns)

maximum :: List Nat -> Nat
maximum Nil = error "Empty list: no maximum value"
maximum (Cons n Nil) = n
maximum (Cons n (Cons n' ns))
  | n > n' = maximum (Cons n ns)
  | otherwise = maximum (Cons n' ns)

-- verifica se uma lista é prefixo de outra
isPrefixOf :: List Nat -> List Nat -> Bool
isPrefixOf Nil _ = True
isPrefixOf (Cons _ _) Nil = False
isPrefixOf (Cons n ns) (Cons m ms) = eq n m && isPrefixOf ns ms

-- ----------------------------------
-- Funções de List a
-- ----------------------------------
(++) :: List a -> List a -> List a
(Cons x xs) ++ ys = Cons x (xs ++ ys)
Nil ++ ys = ys

reverse :: List a -> List a
reverse (Cons x xs) = reverse xs ++ Cons x Nil
reverse Nil = Nil

map :: (a -> b) -> List a -> List b
map f (Cons x xs) = Cons (f x) (map f xs)
map _ Nil = Nil

length :: List a -> Nat
length (Cons _ xs) = S (length xs)
length Nil = O

index :: Nat -> List a -> a
index O (Cons x _) = x
index (S n) (Cons _ xs) = index n xs
index _ Nil = error "Out of range"

-- inicio e fim de uma lista
head :: List a -> a
head = index O

last :: List a -> a
last Nil = error "Empty List: no last element"
last (Cons x Nil) = x
last (Cons _ xs) = last xs

-- elementos de uma lista menos o final/inicial de uma lista
init :: List a -> List a
init Nil = error "Empty List"
init (Cons _ Nil) = Nil
init (Cons x xs) = Cons x (init xs)

tail :: List a -> List a
tail Nil = error "Empty List"
tail (Cons _ xs) = xs

-- take e drop
take :: Nat -> List a -> List a
take O _ = Nil
take (S _) Nil = Nil
take (S n) (Cons x xs) = Cons x (take n xs)

drop :: Nat -> List a -> List a
drop O xs = xs
drop (S _) Nil = Nil
drop (S n) (Cons _ xs) = drop n xs

-- elemIndices :: a -> List a -> List Nat
-- elemIndices _ Nil = Nil
-- elemIndices a (Cons x xs)
--  | eq a x = Cons

-- all e any
all :: (a -> Bool) -> List a -> Bool
all f (Cons x xs) = f x && all f xs
all _ Nil = True

any :: (a -> Bool) -> List a -> Bool
any f (Cons x xs) = f x || any f xs
any _ Nil = False

-- A fold recebe uma função, um valor base e uma lista. Após isso, aplica a função nos elementos da lista e no valor base
fold :: (a -> a -> a) -> a -> List a -> a
fold f e (Cons x xs) = f x (fold f e xs)
fold _ e Nil = e

-- mistura duas listas entre si
mix :: List a -> List a -> List a
mix xs Nil = xs
mix Nil ys = ys
mix (Cons x xs) (Cons y ys) = Cons x (Cons y (mix xs ys))

-- adiciona um elemento entre os elementos de uma lista
intersperse :: a -> List a -> List a
intersperse _ Nil = Nil
intersperse _ (Cons x Nil) = Cons x Nil
intersperse a (Cons x xs) = Cons x (Cons a (intersperse a xs))

replicate :: Nat -> a -> List a
replicate O _ = Nil
replicate (S n) a = Cons a (replicate n a)

-- ----------------------------------
-- Funções safe
-- ----------------------------------
safeHead :: List a -> Maybe a
safeHead Nil = Nothing
safeHead (Cons x _) = Just x

safeLast :: List a -> Maybe a
safeLast Nil = Nothing
safeLast (Cons x Nil) = Just x
safeLast (Cons _ xs) = safeLast xs

safeInit :: List a -> Maybe (List a)
safeInit Nil = Nothing
safeInit xs = Just (init xs)

safeTail :: List a -> Maybe (List a)
safeTail Nil = Nothing
safeTail (Cons _ Nil) = Nothing
safeTail (Cons _ xs) = Just xs

-- findFirst e find
-- findFirst :: a -> List a -> Maybe a
-- findFirst x Nil = Nothing
-- findFirst x (Cons y _)
--   | eq x y =

-- safePick e safeFindFirst
safePick :: Nat -> List a -> Maybe a
safePick _ Nil = Nothing
safePick O (Cons x _) = Just x
safePick (S n) (Cons _ xs) = safePick n xs

-- safeFindFirst

main :: IO ()
main = putStrLn "Hello, world!"