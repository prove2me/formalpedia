-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weight_bound_implies_quotient_sum
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weight_bound_implies_quotient_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T20:33:52.609893+00:00
-- url     : https://prove2.me/theorems/7cbbf976-2498-46b2-94ce-508792329795
-- title:
--   Weighted bound implies an integer quotient capacity
-- statement:
--   The weighted real lower bound, together with positive coordinate scales, forces the sum of the integer quotient capacities to be at least n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weight_bound_implies_quotient_sum
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (d : Fin (m + 1) →₀ ℕ)
    (hweight : (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ)) :
    n ≤ ∑ i, d i / e i := by
  sorry
