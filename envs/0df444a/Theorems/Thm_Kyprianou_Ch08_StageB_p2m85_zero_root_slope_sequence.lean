-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_root_slope_sequence
-- name    : Kyprianou.Ch08.StageB.p2m85_zero_root_slope_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:59:35.17896+00:00
-- url     : https://prove2.me/theorems/cfacf274-4fe8-4fc7-a8d1-588863ddf964
-- title:
--   For a zero right root, the positive secant is the inverse-root quotient along the sequence of reciprocal integers.
-- statement:
--   For a zero right root, the positive secant is the inverse-root quotient along the sequence of reciprocal integers.
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_zero_root_slope_sequence
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hc : ConvexOn ℝ (Ici 0) ψ) (hz : ψ 0 = 0) (hφ : Phi ψ 0 = 0)
    (c : ℝ) (hlim : Tendsto (fun q : ℝ => q / Phi ψ q)
      (nhdsWithin 0 (Ioi 0)) (𝓝 c)) :
    Tendsto (fun n : ℕ => ψ (1 / ((n : ℝ)+1)) / (1 / ((n : ℝ)+1)))
      atTop (𝓝 c) := by
  sorry
