import Mathlib

/- A192473: coefficient of X in 1 + X^n + X^(2*n+2), reduced by X^2 = X+1.
   This file uses explicit degree-<2 representatives; no sorry or axioms are added.
   This is a compilation candidate, not yet kernel-verified. -/

namespace Barker473

-- Coordinates (constant coefficient, coefficient of X) of X^n.
def fibPair : Nat → Int × Int
  | 0 => (1, 0)
  | 1 => (0, 1)
  | n + 2 =>
      ((fibPair (n + 1)).1 + (fibPair n).1,
       (fibPair (n + 1)).2 + (fibPair n).2)

-- Coordinates of X^(2*n+2) = (X^2)^(n+1).
def pellPair : Nat → Int × Int
  | 0 => (1, 1)
  | 1 => (2, 3)
  | n + 2 =>
      (3 * (pellPair (n + 1)).1 - (pellPair n).1,
       3 * (pellPair (n + 1)).2 - (pellPair n).2)

private theorem fib_fst (n : Nat) :
    (fibPair (n + 2)).1 = (fibPair (n + 1)).1 + (fibPair n).1 := by
  rw [fibPair]

private theorem fib_snd (n : Nat) :
    (fibPair (n + 2)).2 = (fibPair (n + 1)).2 + (fibPair n).2 := by
  rw [fibPair]

private theorem pell_fst (n : Nat) :
    (pellPair (n + 2)).1 = 3 * (pellPair (n + 1)).1 - (pellPair n).1 := by
  rw [pellPair]

private theorem pell_snd (n : Nat) :
    (pellPair (n + 2)).2 = 3 * (pellPair (n + 1)).2 - (pellPair n).2 := by
  rw [pellPair]

-- The X coefficient; the additional constant polynomial 1 contributes zero.
def a192473 (n : Nat) : Int := (fibPair n).2 + (pellPair n).2

-- Product (T^2-T-1)(T^2-3T+1) annihilates the sum.
theorem a192473_recurrence (n : Nat) :
    a192473 (n + 4) =
      4 * a192473 (n + 3) - 3 * a192473 (n + 2) -
      2 * a192473 (n + 1) + a192473 n := by
  have f0 := fib_snd n
  have f1 := fib_snd (n + 1)
  have f2 := fib_snd (n + 2)
  have g0 := pell_snd n
  have g1 := pell_snd (n + 1)
  have g2 := pell_snd (n + 2)
  dsimp [a192473]
  -- The fourth-order operator factors as the product of the two quadratics.
  linear_combination f2 - 3 * f1 + f0 + g2 - g1 - g0

-- Evaluation bridges: any element satisfying X^2 = X+1 gives the same pairs.
theorem fibPair_eval {R : Type*} [CommRing R]
    (x : R) (hx : x ^ 2 = x + 1) (n : Nat) :
    ((fibPair n).1 : R) + ((fibPair n).2 : R) * x = x ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fibPair]
  | one => simp [fibPair]
  | more n ih0 ih1 =>
      have hpow : x ^ (n + 2) = x ^ (n + 1) + x ^ n := by
        calc
          x ^ (n + 2) = x ^ n * x ^ 2 := by rw [pow_add]
          _ = x ^ (n + 1) + x ^ n := by rw [hx, pow_succ]; ring
      rw [fibPair]
      simp only [Prod.fst, Prod.snd]
      push_cast
      calc
        ((fibPair (n + 1)).1 : R) + (fibPair n).1 +
            (((fibPair (n + 1)).2 : R) + (fibPair n).2) * x =
            (((fibPair (n + 1)).1 : R) + (fibPair (n + 1)).2 * x) +
            (((fibPair n).1 : R) + (fibPair n).2 * x) := by ring
        _ = x ^ (n + 2) := by rw [ih1, ih0, hpow]

theorem pellPair_eval {R : Type*} [CommRing R]
    (x : R) (hx : x ^ 2 = x + 1) (n : Nat) :
    ((pellPair n).1 : R) + ((pellPair n).2 : R) * x = (x ^ 2) ^ (n + 1) := by
  have hy : (x ^ 2) ^ 2 = 3 * (x ^ 2) - 1 := by
    linear_combination (x ^ 2 + x - 1) * hx
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [pellPair, Prod.fst, Prod.snd]
      push_cast
      rw [hx]
      ring
  | one =>
      simp only [pellPair, Prod.fst, Prod.snd]
      push_cast
      rw [hy, hx]
      ring
  | more n ih0 ih1 =>
      have hpow : (x ^ 2) ^ (n + 2 + 1) =
          3 * (x ^ 2) ^ (n + 1 + 1) - (x ^ 2) ^ (n + 1) := by
        have h : (x ^ 2) ^ (n + 3) = (x ^ 2) ^ (n + 1) * (x ^ 2) ^ 2 := by
          rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
        rw [show n + 2 + 1 = n + 3 by omega, h, hy]
        rw [show n + 1 + 1 = n + 2 by omega]
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
      rw [pellPair]
      simp only [Prod.fst, Prod.snd]
      push_cast
      calc
        3 * ((pellPair (n + 1)).1 : R) - (pellPair n).1 +
            (3 * ((pellPair (n + 1)).2 : R) - (pellPair n).2) * x =
            3 * (((pellPair (n + 1)).1 : R) + (pellPair (n + 1)).2 * x) -
            (((pellPair n).1 : R) + (pellPair n).2 * x) := by ring
        _ = (x ^ 2) ^ (n + 2 + 1) := by rw [ih1, ih0, hpow]

-- This is the exact algebraic evaluation of the OEIS defining polynomial.
theorem a192473_polynomial_bridge {R : Type*} [CommRing R]
    (x : R) (hx : x ^ 2 = x + 1) (n : Nat) :
    (1 : R) + x ^ n + x ^ (2 * n + 2) =
      (1 + ((fibPair n).1 : R) + ((pellPair n).1 : R)) +
      (a192473 n : R) * x := by
  have hf := fibPair_eval x hx n
  have hg := pellPair_eval x hx n
  rw [show 2 * n + 2 = 2 * (n + 1) by omega]
  rw [show x ^ (2 * (n + 1)) = (x ^ 2) ^ (n + 1) by rw [pow_mul]]
  rw [← hf, ← hg]
  dsimp [a192473]
  push_cast
  ring

#print axioms a192473_recurrence
#print axioms fibPair_eval
#print axioms pellPair_eval
#print axioms a192473_polynomial_bridge

end Barker473
