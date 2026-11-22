-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_down_passage_brackets
-- name    : Kyprianou.Ch08.StageB.source_result81_avram_down_passage_brackets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:14:00.153819+00:00
-- url     : https://prove2.me/theorems/86ef535c-7e49-430c-9d46-150282479b3e
-- title:
--   Strict first passage brackets the finite-horizon reflected infimum
-- statement:
--   A strict crossing before the horizon implies that the reflected infimum exceeds the reserve, and the latter event implies that the first strict passage is no later than the horizon. The inequalities encode the possible distinction at a passage exactly at the horizon. Right continuity gives passage time zero when the starting reserve is negative.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, identity (8.6). Mathematical reduction of 80e7c39b-072e-47d5-a5d3-7fe26d044dc0.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_avram_down_passage_brackets
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (ω : Ω) (t : ℝ≥0) :
    let τ := tauMinus (shifted X.X x) 0 ω
    let R := -sInf {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X.X u ω}
    (τ < (t : WithTop ℝ≥0) → x < R) ∧ (x < R → τ ≤ (t : WithTop ℝ≥0)) := by
  sorry
