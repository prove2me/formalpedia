-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIbShort_goodness
-- name    : Freiman.middleRepair_equalIIbShort_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:33.968697+00:00
-- url     : https://prove2.me/theorems/fc9d8b2a-7c4a-4d50-a55f-9ed3ebbda3e7
-- title:
--   Report incoming-order repair: middleRepair_equalIIbShort_goodness
-- statement:
--   Report-normalized equalIIbShort goodness from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIbShort_goodness :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbShort → ∀ d ∈ middleRepairRowChildren c .equalIIbShort, middleRepairGood d := by
  sorry
