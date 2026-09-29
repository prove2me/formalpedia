-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIbNormal_goodness
-- name    : Freiman.middleRepair_equalIIbNormal_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:31.136983+00:00
-- url     : https://prove2.me/theorems/47098fea-90f0-4f7e-8122-2b468a797461
-- title:
--   Report incoming-order repair: middleRepair_equalIIbNormal_goodness
-- statement:
--   Report-normalized equalIIbNormal goodness from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIbNormal_goodness :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbNormal → ∀ d ∈ middleRepairRowChildren c .equalIIbNormal, middleRepairGood d := by
  sorry
