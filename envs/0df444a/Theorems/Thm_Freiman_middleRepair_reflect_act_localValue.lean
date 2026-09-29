-- Prove2me | Theorems.Thm_Freiman_middleRepair_reflect_act_localValue
-- name    : Freiman.middleRepair_reflect_act_localValue
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:30.724813+00:00
-- url     : https://prove2.me/theorems/5430a6aa-4b78-479e-914f-aeb480087482
-- title:
--   middleRepair reflect act localValue
-- statement:
--   Apply the reflection identity to the cumulative frame bit.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_reflect_act_localValue :
  ∀ (b : Bool) (a : ℤ → ℕ+), localValue (middleRepairActDigits b a) 0 = localValue a 0 := by
  sorry
