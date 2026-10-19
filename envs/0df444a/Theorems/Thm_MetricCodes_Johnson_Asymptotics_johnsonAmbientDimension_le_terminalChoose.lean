-- Prove2me | Theorems.Thm_MetricCodes_Johnson_Asymptotics_johnsonAmbientDimension_le_terminalChoose
-- name    : MetricCodes.Johnson.Asymptotics.johnsonAmbientDimension_le_terminalChoose
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:24.606098+00:00
-- url     : https://prove2.me/theorems/d9b051d3-10b1-4f39-a31e-568f9ad05a35
-- title:
--   MetricCodes.Johnson.Asymptotics.johnsonAmbientDimension_le_terminalChoose
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

theorem MetricCodes.Johnson.Asymptotics.johnsonAmbientDimension_le_terminalChoose
    {n w p q L : ℕ}
    (h : MetricCodes.Johnson.AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L ≤ n.choose L := by sorry
