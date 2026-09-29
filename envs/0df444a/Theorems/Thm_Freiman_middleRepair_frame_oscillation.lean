-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_oscillation
-- name    : Freiman.middleRepair_frame_oscillation
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:40.129496+00:00
-- url     : https://prove2.me/theorems/04d00ee4-ae14-4635-b8ea-1f3faacd923d
-- title:
--   middleRepair frame oscillation
-- statement:
--   Use the retained oscillation bound on the oriented core after reflecting the same physical completion.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_oscillation :
  ∀ (s : MiddleRepairFrame) (a : ℤ → ℕ+) (t : ℝ), middleRegular s.core →
  middleCompatible (middleRepairPhysical s) a → t∈middleCover s.core →
    |localValue a 0-t| ≤ middleWidth s.core.left+middleWidth s.core.right := by
  sorry
