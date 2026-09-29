-- Prove2me | Theorems.Thm_HorizontalPadicL_exists_prime_quadraticCharacter_prescribed_sign
-- name    : HorizontalPadicL.exists_prime_quadraticCharacter_prescribed_sign
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:17:12.068782+00:00
-- url     : https://prove2.me/theorems/5daba92b-2203-45ed-a886-7f3f32e5fbf7
-- title:
--   Arbitrarily large prime-conductor quadratic characters with prescribed parity
-- statement:
--   Let $A$ be a positive integer, let $b\ge0$, and choose a sign $s\in\{1,-1\}$. There is a prime $q>b$ and a primitive Dirichlet character $\eta$ of modulus and conductor $q$ such that
--
--   $$q\equiv s\pmod{8A},\qquad \operatorname{ord}(\eta)=2,\qquad (A,q)=1,\qquad\eta(-1)=s.$$
--
--   Moreover,
--
--   $$\eta(n)=1\qquad\text{for every positive divisor }n\mid A.$$
--
--   Thus quadratic characters of either parity can be chosen with arbitrarily large prime conductor avoiding a prescribed finite set, while being trivial at the corresponding unramified local components. The conductor congruence also makes every even nebentype of level dividing $A$ take value one at $q$. This provides the arithmetic seed used in the horizontal nonvanishing argument; it asserts no nonvanishing of a modular $L$-value.
--
--   **Formalization Note.** The sign is encoded by a Boolean, with `true` corresponding to $1$. Characters take values in the fixed algebraic closure of the rationals and are paired with their positive levels. Primitivity identifies this level with the conductor.
-- source:
--   A derived consequence of Dirichlet's theorem and quadratic reciprocity, formalized directly from Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. Dirichlet: Mathlib/NumberTheory/LSeries/PrimesInAP.lean, Nat.forall_exists_prime_gt_and_eq_mod, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/PrimesInAP.lean#L443. Reciprocity and supplementary law at two: Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean, quadraticChar_odd_prime and quadraticChar_two, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean#L93 and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean#L37. The theorem combines these established results with the prime-modulus conductor criterion; it is not claimed as a verbatim theorem from a paper.

import Definitions.Def_KN_HorizontalPadicL

set_option autoImplicit false

theorem HorizontalPadicL.exists_prime_quadraticCharacter_prescribed_sign
    (A : ℕ) (hA : 0 < A) (s : Bool) (b : ℕ) :
    ∃ η : DirichletCharacterWithLevel,
      η.1.1.Prime ∧ b < η.1.1 ∧
      (η.1.1 : ZMod (8 * A)) = (if s then 1 else -1) ∧
      η.2.IsPrimitive ∧ orderOf η.2 = 2 ∧ Nat.Coprime A η.2.conductor ∧
      η.2 (-1) = (if s then 1 else -1) ∧
      (∀ n : ℕ, 0 < n → n ∣ A → η.2 n = 1) := by sorry
