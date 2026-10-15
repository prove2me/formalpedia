-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coefficient_vanishing_implies_support_weight_bound
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coefficient_vanishing_implies_support_weight_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T18:09:28.478268+00:00
-- url     : https://prove2.me/theorems/40e0ef93-98e6-453a-b2ff-c5b07fb82297
-- title:
--   Coefficient vanishing forces a support weight bound
-- statement:
--   Every exponent in the support of Q has weighted degree at least the cutoff, because any exponent below it has zero coefficient. The statement uses the exact exponent-vector encoding from the interpolation definitions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coefficient_vanishing_implies_support_weight_bound
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoord : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, ρ i * (a i : ℝ)) < (((n + m : ℕ) : ℝ) * R) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q = 0) :
    ∀ d ∈ Q.support,
      (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ) := by sorry
