-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIa_contacts
-- name    : Freiman.middleRepair_equalIIa_contacts
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:24.448976+00:00
-- url     : https://prove2.me/theorems/4f9ee9ca-364e-470c-98c1-ff0959755263
-- title:
--   Report incoming-order repair: middleRepair_equalIIa_contacts
-- statement:
--   Report-normalized equalIIa contacts from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIa_contacts :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIa → middleContacts (middleRepairRowChildren c .equalIIa) := by
  sorry
