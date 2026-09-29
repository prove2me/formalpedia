-- Prove2me | Theorems.Thm_Freiman_middleRepair_mixedA_contacts
-- name    : Freiman.middleRepair_mixedA_contacts
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:02.953594+00:00
-- url     : https://prove2.me/theorems/57a2acdf-c593-488d-92bb-db68f74dadf2
-- title:
--   Report incoming-order repair: middleRepair_mixedA_contacts
-- statement:
--   Report-normalized mixedA contacts from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_mixedA_contacts :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .mixedA → middleContacts (middleRepairRowChildren c .mixedA) := by
  sorry
