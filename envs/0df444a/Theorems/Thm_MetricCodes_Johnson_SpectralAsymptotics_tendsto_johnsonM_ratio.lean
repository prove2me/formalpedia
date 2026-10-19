-- Prove2me | Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonM_ratio
-- name    : MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonM_ratio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:27.636998+00:00
-- url     : https://prove2.me/theorems/fd8a5200-24bf-48b6-b215-174533360f4d
-- title:
--   MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonM_ratio
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics

theorem MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonM_ratio
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredWeight a / 2)) := by sorry
