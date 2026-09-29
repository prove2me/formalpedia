-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_interpret_contacts
-- name    : Freiman.middleRepair_cert_interpret_contacts
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:08.715495+00:00
-- url     : https://prove2.me/theorems/423ef3fb-2c11-498c-9ed7-f8314443a224
-- title:
--   Report incoming-order repair: middleRepair_cert_interpret_contacts
-- statement:
--   Read the finite validity and both adjacent comparison roles as closed-interval contacts. Children are constructed in normalized-parent order and normalized again before subsequent forks.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem Freiman.middleRepair_cert_interpret_contacts :
    (∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2))) → (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ (c : MiddleCore) (f : Fin 9), middleRepairCertDomain c f.val → middleRepairCertActualFamily c f.val → middleContacts (middleRepairRowChildren c (middleCertRow f.val)) := by
  sorry
