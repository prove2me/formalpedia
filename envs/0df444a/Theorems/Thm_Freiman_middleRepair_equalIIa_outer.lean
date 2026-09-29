-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIa_outer
-- name    : Freiman.middleRepair_equalIIa_outer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:27.69398+00:00
-- url     : https://prove2.me/theorems/818bd5bb-66ff-4bb8-aebd-2c535353817a
-- title:
--   Report incoming-order repair: middleRepair_equalIIa_outer
-- statement:
--   Report-normalized equalIIa outer from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIa_outer :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIa → middleOuter c (middleRepairRowChildren c .equalIIa) := by
  sorry
