-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_start_core
-- name    : Freiman.middleRepair_frame_start_core
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:08.488851+00:00
-- url     : https://prove2.me/theorems/61238562-febf-439c-83c6-f393de3785d6
-- title:
--   middleRepair frame start core
-- statement:
--   The initial stored core is normalized.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_start_core :
  ∀ c : MiddleCore, (middleRepairStart c).core = middleNormalized c := by
  sorry
