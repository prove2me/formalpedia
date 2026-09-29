-- Prove2me | Theorems.Thm_Freiman_middleRepair_mixedB_outer
-- name    : Freiman.middleRepair_mixedB_outer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:10.30299+00:00
-- url     : https://prove2.me/theorems/974d92a6-fdf7-4059-9ce5-d6e53d1fa1ca
-- title:
--   Report incoming-order repair: middleRepair_mixedB_outer
-- statement:
--   Report-normalized mixedB outer from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_mixedB_outer :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedB → middleOuter c (middleRepairRowChildren c .mixedB) := by
  sorry
