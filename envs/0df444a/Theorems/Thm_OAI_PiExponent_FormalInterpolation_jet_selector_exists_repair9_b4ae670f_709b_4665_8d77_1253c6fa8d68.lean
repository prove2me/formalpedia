-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_jet_selector_exists_repair9_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- name    : OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair9_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:00:09.528277+00:00
-- url     : https://prove2.me/theorems/3837792d-5f17-4283-9249-108bb4e0fff5
-- title:
--   Separating selectors for finite Taylor jets
-- statement:
--   For a chosen center and exponent, construct a polynomial whose bounded translated coefficients are one at that jet and zero at every other bounded jet. If α has degree greater than D, the zero polynomial suffices because it cannot equal any bounded β. Otherwise, prescribe the single monomial jet at j and zero jets at all other centers. This removes jet separation from the parent. A proof route is to identify bounded translated coefficients with classes modulo the (D+1)st power of the point maximal ideal, prove distinct point ideals are comaximal using injectivity of c, and apply the finite Chinese remainder theorem to their powers. The boundary cases D = 0 and empty J are consistent with the statement. The remaining core is formalizing the local-coordinate correspondence and the powered-ideal CRT application.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair9_b4ae670f_709b_4665_8d77_1253c6fa8d68
    {n : Nat} {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i : Fin n, β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 := by sorry
