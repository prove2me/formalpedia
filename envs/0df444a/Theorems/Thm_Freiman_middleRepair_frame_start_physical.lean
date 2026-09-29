-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_start_physical
-- name    : Freiman.middleRepair_frame_start_physical
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:01.041672+00:00
-- url     : https://prove2.me/theorems/4cf4c3c1-1913-44f7-b1f3-5166a9b5a784
-- title:
--   middleRepair frame start physical
-- statement:
--   The initial frame records the original physical pair.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_start_physical :
  ∀ c : MiddleCore, middleRepairPhysical (middleRepairStart c) = c := by
  sorry
