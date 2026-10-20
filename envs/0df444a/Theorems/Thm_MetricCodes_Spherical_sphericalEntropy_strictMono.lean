-- Prove2me | Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono
-- name    : MetricCodes.Spherical.sphericalEntropy_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:29.434958+00:00
-- url     : https://prove2.me/theorems/a8e651f0-bc96-4238-ba93-cb77b01607d3
-- title:
--   MetricCodes.Spherical.sphericalEntropy_strictMono
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section

theorem MetricCodes.Spherical.sphericalEntropy_strictMono :
    StrictMonoOn MetricCodes.sphericalEntropy (Set.Ici (0 : ℝ)) := by sorry
