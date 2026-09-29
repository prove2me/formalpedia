-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_normalized_good
-- name    : Freiman.middleRepair_frame_normalized_good
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:09.080734+00:00
-- url     : https://prove2.me/theorems/3a351bea-1544-480b-be81-1ffa778365d9
-- title:
--   middleRepair frame normalized good
-- statement:
--   The two goodness fork children agree after parent normalization.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_normalized_good :
  ∀ c : MiddleCore, middleRepairGood (middleNormalized c) ↔ middleRepairGood c := by
  sorry
