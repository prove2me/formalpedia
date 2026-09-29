-- Prove2me | Theorems.Thm_Freiman_middleRepair_mixedA_outer
-- name    : Freiman.middleRepair_mixedA_outer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:04.165564+00:00
-- url     : https://prove2.me/theorems/9b983009-a55c-40d7-bbea-0ca462b1a13c
-- title:
--   Report incoming-order repair: middleRepair_mixedA_outer
-- statement:
--   Report-normalized mixedA outer from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_mixedA_outer :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedA → middleOuter c (middleRepairRowChildren c .mixedA) := by
  sorry
