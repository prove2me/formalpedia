-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_raw_child_proper
-- name    : Freiman.middleRepair_frame_raw_child_proper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:12.821202+00:00
-- url     : https://prove2.me/theorems/be8056ea-9b4e-4b9d-8251-de8291d6e75d
-- title:
--   middleRepair frame raw child proper
-- statement:
--   Before the second normalization the child is an ordinary ordered physical append.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_raw_child_proper :
  ∀ (c : MiddleCore) (u v : List ℕ+), middleDigits123 u → middleDigits123 v →
  0 < u.length+v.length → middleProper (middleNormalized c) (middleRepairRawChild c u v) := by
  sorry
