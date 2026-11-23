-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_set_integral_mono
-- name    : Kyprianou.Ch08.StageB.scale_slice_lower_hy4_set_integral_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:42:37.388697+00:00
-- url     : https://prove2.me/theorems/5c89e4f3-1249-4799-89df-72813e444b2d
-- title:
--   Set discounted integral bounded by full two-clock payoff integral
-- statement:
--   If a set lies almost everywhere in the up-before-down or infinite-clock event, its discounted-clock set integral is at most the full discounted payoff integral.
-- source:
--   Source-faithful measure-theoretic child of scale_slice_lower_hy4 (795c944f); uses the null-measurable clock event rather than requiring measurability of the no-drawdown set.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.scale_slice_lower_hy4_set_integral_mono
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (U V : Ω → ℝ≥0∞) (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (q : ℝ) (hdi : Integrable (fun ω => discountedAt q (U ω)) μ)
    (hpi : Integrable (fun ω => if U ω < V ω then discountedAt q (U ω) else 0) μ)
    (s : Set Ω) (hsub : s ≤ᵐ[μ] {ω | U ω < V ω ∨ U ω = ⊤}) :
    (∫ ω in s, discountedAt q (U ω) ∂μ) ≤
      ∫ ω, (if U ω < V ω then discountedAt q (U ω) else 0) ∂μ := by
  sorry
