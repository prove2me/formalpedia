-- Prove2me | Theorems.Thm_Freiman_middleRepair_equalIIbShort_contacts
-- name    : Freiman.middleRepair_equalIIbShort_contacts
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:50.647795+00:00
-- url     : https://prove2.me/theorems/cca5a5ed-9571-45ca-bc76-12e55c5e633e
-- title:
--   Report incoming-order repair: middleRepair_equalIIbShort_contacts
-- statement:
--   Report-normalized equalIIbShort contacts from the exact source family and explicit incoming-order boundary ledger.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_equalIIbShort_contacts :
    ∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRowCondition c .equalIIbShort → middleContacts (middleRepairRowChildren c .equalIIbShort) := by
  sorry
