-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_jet_selector_exists_repair7_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- name    : OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair7_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:48:20.620426+00:00
-- url     : https://prove2.me/theorems/a0599817-b45c-4ce2-9f76-d8c4b9ad7dc8
-- title:
--   Separating selectors for finite Taylor jets
-- statement:
--   For any center and exponent, construct a polynomial whose bounded translated coefficients are one at that center and exponent, and zero at every other bounded jet. If α has degree greater than D, the zero polynomial satisfies the conditions because no bounded β equals α. If |α| ≤ D, prescribe its monomial jet at j and zero jets at other centers. The point ideals are pairwise comaximal by injectivity of c; CRT for their (D+1)st powers then gives a polynomial realizing these local classes. This removes the separation step from the parent. The remaining work is formalizing the correspondence between translated coefficients of degree ≤ D and classes modulo the powered point ideal, then applying powered-ideal CRT. The statement is vacuous when J is empty; for D = 0 it reduces to selecting constant values across distinct centers.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair7_b4ae670f_709b_4665_8d77_1253c6fa8d68
    {n : Nat} {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i : Fin n, β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 := by sorry
