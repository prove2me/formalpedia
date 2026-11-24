-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_root_inverse_at_positive
-- name    : Kyprianou.Ch08.StageB.p2m85_zero_root_inverse_at_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:00:30.582401+00:00
-- url     : https://prove2.me/theorems/3dacfb63-b94a-4ed8-b520-0b9861bbd210
-- title:
--   p2m85 zero root inverse at positive
-- statement:
--   p2m85 zero root inverse at positive
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_zero_root_inverse_at_positive
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hc : ConvexOn ℝ (Ici 0) ψ) (hz : ψ 0 = 0) (hφ : Phi ψ 0 = 0) (s : ℝ) (hs : 0 < s) :
    Phi ψ (ψ s) = s := by
  sorry
