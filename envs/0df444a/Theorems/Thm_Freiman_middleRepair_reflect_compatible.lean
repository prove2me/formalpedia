-- Prove2me | Theorems.Thm_Freiman_middleRepair_reflect_compatible
-- name    : Freiman.middleRepair_reflect_compatible
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:27.038986+00:00
-- url     : https://prove2.me/theorems/4e9b0371-3ffe-4d96-b61c-bb4704cfac77
-- title:
--   middleRepair reflect compatible
-- statement:
--   Reflection exchanges the actual two outward prefixes and fixes the central digit.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_reflect_compatible :
  ∀ (c : MiddleCore) (a : ℤ → ℕ+), middleCompatible c a →
  middleCompatible (middleRepairSwap c) (middleRepairReflectDigits a) := by
  sorry
