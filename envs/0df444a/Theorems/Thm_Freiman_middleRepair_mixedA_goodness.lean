-- Prove2me | Theorems.Thm_Freiman_middleRepair_mixedA_goodness
-- name    : Freiman.middleRepair_mixedA_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:01.22398+00:00
-- url     : https://prove2.me/theorems/27cb1dfb-7545-45b0-979b-5686afc59281
-- title:
--   Report incoming-order repair: middleRepair_mixedA_goodness
-- statement:
--   Report-normalized mixedA goodness from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_mixedA_goodness :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedA → ∀ d ∈ middleRepairRowChildren c .mixedA, middleRepairGood d := by
  sorry
