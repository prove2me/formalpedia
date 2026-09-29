-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_compatible_core
-- name    : Freiman.middleRepair_frame_compatible_core
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:32.795081+00:00
-- url     : https://prove2.me/theorems/11c1360f-d58a-46e9-b1c3-145d2b166b7e
-- title:
--   middleRepair frame compatible core
-- statement:
--   Convert a compatible physical completion to the oriented frame core.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_compatible_core :
  ∀ (s : MiddleRepairFrame) (a : ℤ → ℕ+), middleCompatible (middleRepairPhysical s) a →
  middleCompatible s.core (middleRepairActDigits s.reflected a) := by
  sorry
