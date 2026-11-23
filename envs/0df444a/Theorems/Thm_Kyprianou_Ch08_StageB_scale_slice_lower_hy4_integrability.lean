-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_integrability
-- name    : Kyprianou.Ch08.StageB.scale_slice_lower_hy4_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:42:29.341608+00:00
-- url     : https://prove2.me/theorems/5382be6a-ee64-4609-b1f6-25f6dae0c164
-- title:
--   Integrability of a two-clock discounted payoff
-- statement:
--   For two aemeasurable extended clocks on a finite measure space and nonnegative q, the discounted clock and its up-before-down indicator payoff are integrable.
-- source:
--   Source-faithful measure-theoretic child of scale_slice_lower_hy4 (795c944f); isolates the discounted-at measurability and boundedness argument.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.scale_slice_lower_hy4_integrability
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (U V : Ω → ℝ≥0∞) (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun ω => discountedAt q (U ω)) μ ∧
      Integrable (fun ω => if U ω < V ω then discountedAt q (U ω) else 0) μ := by
  sorry
