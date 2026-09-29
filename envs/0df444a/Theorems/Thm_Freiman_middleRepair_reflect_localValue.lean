-- Prove2me | Theorems.Thm_Freiman_middleRepair_reflect_localValue
-- name    : Freiman.middleRepair_reflect_localValue
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:22.026997+00:00
-- url     : https://prove2.me/theorems/650de28a-13a5-42ac-853e-9cb52daac421
-- title:
--   middleRepair reflect localValue
-- statement:
--   Reflection exchanges the two continued-fraction tails at center zero.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_reflect_localValue :
  ∀ a : ℤ → ℕ+, localValue (middleRepairReflectDigits a) 0 = localValue a 0 := by
  sorry
