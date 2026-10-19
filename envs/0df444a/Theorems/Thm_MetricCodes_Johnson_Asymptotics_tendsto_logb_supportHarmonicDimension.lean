-- Prove2me | Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_supportHarmonicDimension
-- name    : MetricCodes.Johnson.Asymptotics.tendsto_logb_supportHarmonicDimension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:24.606098+00:00
-- url     : https://prove2.me/theorems/76add2e0-9e1a-4d6b-a7a6-46bdcbfc4c01
-- title:
--   MetricCodes.Johnson.Asymptotics.tendsto_logb_supportHarmonicDimension
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics

theorem MetricCodes.Johnson.Asymptotics.tendsto_logb_supportHarmonicDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension
            (shellWeight a n) (supportDegree b n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by sorry
