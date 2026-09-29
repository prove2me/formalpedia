-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIJ_goodness
-- name    : Freiman.middleRepair_equalIJ_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:22.152826+00:00
-- url     : https://prove2.me/theorems/9c76907b-4c54-4e3b-9881-7cca63a6cb35
-- title:
--   Report incoming-order repair: middleRepair_equalIJ_goodness
-- statement:
--   Report-normalized equalIJ goodness from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIJ_goodness :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIJ → ∀ d ∈ middleRepairRowChildren c .equalIJ, middleRepairGood d := by
  sorry
