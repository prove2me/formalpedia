-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_overshoot_payoff_eq
-- name    : Kyprianou.Ch08.StageB.p2m810_shifted_overshoot_payoff_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:05:49.720259+00:00
-- url     : https://prove2.me/theorems/e3846cb1-8471-40ec-801f-1dbe073e62c2
-- title:
--   Shifted and unshifted overshoot payoffs agree
-- statement:
--   Shifted and unshifted overshoot payoffs agree
-- source:
--   Kyprianou (2006), Exercise 8.10(iv)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m810_shifted_overshoot_payoff_eq
    {Ω : Type} (X : ℝ≥0 → Ω → ℝ) (q c y : ℝ) :
    downOvershootTilt X q c y = downEsscherPayoff X q c y := by
  sorry
