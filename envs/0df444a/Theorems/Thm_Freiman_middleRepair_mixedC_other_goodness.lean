-- Prove2me | Theorems.Thm_Freiman_middleRepair_mixedC_other_goodness
-- name    : Freiman.middleRepair_mixedC_other_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:48.99163+00:00
-- url     : https://prove2.me/theorems/1295269c-5449-4b69-a770-f57973841faf
-- title:
--   Report incoming-order repair: middleRepair_mixedC_other_goodness
-- statement:
--   Report-normalized mixedC other_goodness from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_mixedC_other_goodness :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedC →
      middleRepairGood (middleRepairChild c [2] []) ∧ middleRepairGood (middleRepairChild c [1] []) := by
  sorry
