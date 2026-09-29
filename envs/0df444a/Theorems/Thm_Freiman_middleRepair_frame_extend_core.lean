-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_extend_core
-- name    : Freiman.middleRepair_frame_extend_core
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:03.940358+00:00
-- url     : https://prove2.me/theorems/6fd4e21e-5e79-4786-b353-67addb9dd0f6
-- title:
--   middleRepair frame extend core
-- statement:
--   Extending a frame has exactly the normalized geometric child as core.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_extend_core :
  ∀ (s : MiddleRepairFrame) (u v : List ℕ+),
  (middleRepairExtend s u v).core = middleRepairChild s.core u v := by
  sorry
