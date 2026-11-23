-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_reflected_regularity_of_cadlag_no_positive_jumps
-- name    : Kyprianou.Ch08.StageB.reflected_regularity_of_cadlag_no_positive_jumps
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:08:28.384844+00:00
-- url     : https://prove2.me/theorems/e0ba16c8-1db5-4a54-b556-939133c79581
-- title:
--   Reflected drawdown path has right continuity, finite left limits, and no downward jumps
-- statement:
--   Given the proved structural facts for the running supremum and absence of positive jumps for the underlying càdlàg path, the reflected drawdown is right continuous, has finite left limits at positive times, and never jumps downward. These are exactly the hypotheses of the proved generic càdlàg upper-semicontinuity theorem.
-- source:
--   Derived from the exact target preamble and the regularity block of the direct candidate. It packages the generic reflection argument separately from the financial/compact-excursion part of the parent theorem.

import Mathlib.Topology.Order.LeftRight
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_of_no_upward_jump

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.reflected_regularity_of_cadlag_no_positive_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : IsCadlag fun t => X t ω) (hX0 : X 0 ω = 0)
    (hmono : Monotone (fun t : ℝ≥0 => runningSup X t ω))
    (hdom : ∀ t : ℝ≥0, X t ω ≤ runningSup X t ω)
    (hrepr : ∀ T : ℝ≥0, runningSup X T ω = ⨆ u : Icc (0 : ℝ≥0) T, X u.1 ω)
    (hNoUp : ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l) → X t ω ≤ l) :
    (∀ t : ℝ≥0, ContinuousWithinAt (fun s : ℝ≥0 => reflectAtSup X 0 s ω) (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => reflectAtSup X 0 s ω) (nhdsWithin t (Iio t)) (nhds l)) ∧
    (∀ (t : ℝ≥0) (l : ℝ), 0 < t → Tendsto (fun s : ℝ≥0 => reflectAtSup X 0 s ω) (nhdsWithin t (Iio t)) (nhds l) → l ≤ reflectAtSup X 0 t ω) := by sorry
