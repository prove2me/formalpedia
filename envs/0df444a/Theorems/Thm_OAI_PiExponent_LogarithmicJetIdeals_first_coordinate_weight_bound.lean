-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_first_coordinate_weight_bound
-- name    : OAI.PiExponent.LogarithmicJetIdeals.first_coordinate_weight_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:59:14.176174+00:00
-- url     : https://prove2.me/theorems/560939cf-bfdc-4235-aeaa-bc3c375b0201
-- title:
--   Weighted degree forces the first exponent below its scale
-- statement:
--   A strict weighted-degree bound below R, together with the lower scale bound on every generator exponent and positivity of the weights, forces the zeroth exponent of b to be strictly less than the zeroth generator exponent. This remains valid when m = 0; when the zeroth generator exponent is zero the hypotheses are contradictory.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.first_coordinate_weight_bound
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ)
    (R : ℝ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (b : Fin (m + 1) → ℕ)
    (hb : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R) :
    b (0 : Fin (m + 1)) < e (0 : Fin (m + 1)) := by sorry
