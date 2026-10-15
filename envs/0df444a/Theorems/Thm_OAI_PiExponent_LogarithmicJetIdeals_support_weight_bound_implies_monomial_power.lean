-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_support_weight_bound_implies_monomial_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.support_weight_bound_implies_monomial_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T18:10:00.175959+00:00
-- url     : https://prove2.me/theorems/7a6f94f2-bea0-47cf-8f79-31a78e5cbe6c
-- title:
--   A weighted support bound implies coordinate monomial ideal power membership
-- statement:
--   If every support exponent has weighted degree at least the cutoff, then each has enough coordinatewise multiples of the generator exponents to be divisible by a product of n generators. The bound remains valid at equality and for n = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.support_weight_bound_implies_monomial_power
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hsupport : ∀ d ∈ Q.support,
      (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ)) :
    Q ∈ (Ideal.span (Set.range (fun i : Fin (m + 1) =>
      MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by sorry
