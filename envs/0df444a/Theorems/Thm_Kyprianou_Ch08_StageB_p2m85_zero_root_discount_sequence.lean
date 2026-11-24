-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_root_discount_sequence
-- name    : Kyprianou.Ch08.StageB.p2m85_zero_root_discount_sequence
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:00:49.968732+00:00
-- url     : https://prove2.me/theorems/c2d91d08-9500-4efa-84f4-f0d8c82dacf1
-- title:
--   p2m85 zero root discount sequence
-- statement:
--   p2m85 zero root discount sequence
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_zero_root_discount_sequence
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hc : ConvexOn ℝ (Ici 0) ψ) (hz : ψ 0 = 0) (hφ : Phi ψ 0 = 0) :
    Tendsto (fun n : ℕ => ψ (1 / ((n : ℝ)+1))) atTop (nhdsWithin 0 (Ioi 0)) := by
  sorry
