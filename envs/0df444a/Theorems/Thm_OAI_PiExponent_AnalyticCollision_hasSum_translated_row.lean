-- Prove2me | Theorems.Thm_OAI_PiExponent_AnalyticCollision_hasSum_translated_row
-- name    : OAI.PiExponent.AnalyticCollision.hasSum_translated_row
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:01:02.758001+00:00
-- url     : https://prove2.me/theorems/b3883f67-33d9-4c82-a1e0-4470391786cd
-- title:
--   Taylor expansion of a translated Cauchy row
-- statement:
--   The normalized Taylor series of `f` converges at the translated logarithmic argument, and the Cauchy row functional can be passed through that series using the geometric majorant. The positive radius and center margin ensure convergence on the whole half-radius circle; `hD` supplies the summable coefficient majorant.

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open Filter Topology

theorem OAI.PiExponent.AnalyticCollision.hasSum_translated_row {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : NNReal} (hR : 0 < R) {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f z‖ ≤ D) {center : ℂ} (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) : HasSum (fun d => cauchyPowerSeries (fun t : ℂ => (((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)) 0 (1 / 2) ell (fun _ => (1 : ℂ)) * cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ))) (cauchyPowerSeries (fun t : ℂ => f (center + Complex.log (1 + t))) 0 (1 / 2) ell (fun _ => (1 : ℂ))) := by sorry
