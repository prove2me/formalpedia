-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_normalize_core
-- name    : Freiman.middleRepair_frame_normalize_core
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:12.578914+00:00
-- url     : https://prove2.me/theorems/87c15614-f204-4aa2-9b33-36ae42c2a7a6
-- title:
--   middleRepair frame normalize core
-- statement:
--   The frame normalization uses exactly the report core normalization.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_normalize_core :
  ∀ s : MiddleRepairFrame,
  (middleRepairNormalizeFrame s).core = middleNormalized s.core := by
  sorry
