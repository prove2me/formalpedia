-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIa_goodness
-- name    : Freiman.middleRepair_equalIIa_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:33.198708+00:00
-- url     : https://prove2.me/theorems/18f2ddf3-2a9f-4645-8ce5-065a1784c618
-- title:
--   Report incoming-order repair: middleRepair_equalIIa_goodness
-- statement:
--   Report-normalized equalIIa goodness from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIa_goodness :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIa → ∀ d ∈ middleRepairRowChildren c .equalIIa, middleRepairGood d := by
  sorry
