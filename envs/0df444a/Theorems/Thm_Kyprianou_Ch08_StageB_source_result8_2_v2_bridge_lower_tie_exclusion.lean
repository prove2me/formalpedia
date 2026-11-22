-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_lower_tie_exclusion
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_lower_tie_exclusion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:56:01.7388+00:00
-- url     : https://prove2.me/theorems/7b552dce-34cd-43a3-aea4-96269766a81a
-- title:
--   Bridge 8.2 helper: no-drawdown with finite up-crossing implies up-before-down on good paths
-- statement:
--   On a cadlag path without positive jumps starting at 0, if the drawdown stays below l before the up-crossing of d and the up-crossing is finite, then the up-crossing strictly precedes the down-crossing of -l. Strict down-before-up yields an sInf witness below -l whose drawdown exceeds l; a finite tie transfers to the proved strict exit geometry on the path shifted by l, which forces the clocks to be infinite. This discharges the per-path core of lower slice 795c944f (frontier group E01 of bridge efd9aabc).
-- source:
--   Minimum source-faithful descendant of Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_lower [795c944f-7070-4a09-b77f-8e35067898de] (child of bridge efd9aabc-cb4e-4443-a2e5-0c09c61782a3). The lower comparison is not a pointwise inclusion (never-exit paths lie in N vacuously), so the AE inclusion must be built per-path here and assembled with D.levy.cadlag_ae plus proved no_positive_jumps in the parent. Pure statement over abstract X to avoid duplicating model binders.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_lower_tie_exclusion
    {Ω : Type} (X : ℝ≥0 → Ω → ℝ) (hX0 : ∀ ω, X 0 ω = 0) :
    ∀ l d : ℝ, 0 < l → 0 < d → ∀ ω : Ω,
      IsCadlag (fun s => X s ω) →
      (∀ s : ℝ≥0, ∀ v : ℝ, 0 < s →
        Tendsto (fun s => X s ω) (nhdsWithin s (Iio s)) (nhds v) → X s ω ≤ v) →
      NoDrawdownBeforeUpcrossing X d l ω → tauPlus X d ω < ⊤ →
      tauPlus X d ω < tauMinus X (-l) ω := by
  sorry
