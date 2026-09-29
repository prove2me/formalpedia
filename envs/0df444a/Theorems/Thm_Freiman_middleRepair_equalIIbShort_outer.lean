-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIbShort_outer
-- name    : Freiman.middleRepair_equalIIbShort_outer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:36.727251+00:00
-- url     : https://prove2.me/theorems/08dbaacf-bbe2-40b5-9b52-09ceece04916
-- title:
--   Report incoming-order repair: middleRepair_equalIIbShort_outer
-- statement:
--   Report-normalized equalIIbShort outer from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIbShort_outer :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbShort → middleOuter c (middleRepairRowChildren c .equalIIbShort) := by
  sorry
