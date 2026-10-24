-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_jet_selector_exists_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- name    : OAI.PiExponent.FormalInterpolation.jet_selector_exists_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:58:32.828269+00:00
-- url     : https://prove2.me/theorems/55a367a8-d26f-4d91-988b-3158e19db30c
-- title:
--   Separating selectors for finite Taylor jets
-- statement:
--   For a center j and exponent α, construct a polynomial that selects precisely that translated coefficient among all jets of total degree at most D. The concrete route is to represent the local monomial jet modulo the (D+1)-st power of the maximal ideal at c j, assign zero classes at the other centers, and use the Chinese remainder theorem. If α has degree greater than D, its prescribed bounded-jet selector is zero. Pairwise comaximality follows from injectivity of c: distinct centers differ in some coordinate. This child removes the global separation step; proving the quotient-to-coefficient correspondence and the powered-ideal CRT application remains its core obligation.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.jet_selector_exists_b4ae670f_709b_4665_8d77_1253c6fa8d68
    {n : Nat} {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i ∈ (Finset.univ : Finset (Fin n)), β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 := by sorry
