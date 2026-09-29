-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIbNormal_outer
-- name    : Freiman.middleRepair_equalIIbNormal_outer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:39.602344+00:00
-- url     : https://prove2.me/theorems/532e172a-9513-468c-a049-026aebf832cb
-- title:
--   Report incoming-order repair: middleRepair_equalIIbNormal_outer
-- statement:
--   Report-normalized equalIIbNormal outer from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIbNormal_outer :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbNormal → middleOuter c (middleRepairRowChildren c .equalIIbNormal) := by
  sorry
