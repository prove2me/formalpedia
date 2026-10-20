-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_rational_log_upper
-- name    : MetricCodes.Spherical.HigherHierarchy.Numerics.rational_log_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:34.786068+00:00
-- url     : https://prove2.me/theorems/883931c9-2d29-4b3f-b3d6-3788108900f8
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Numerics.rational_log_upper
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy.Numerics

theorem MetricCodes.Spherical.HigherHierarchy.Numerics.rational_log_upper {r hi : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hhi : MetricCodes.Numerics.logSeriesUpper
      ((r - 1) / (r + 1)) m < hi) : Real.log r < hi := by sorry
