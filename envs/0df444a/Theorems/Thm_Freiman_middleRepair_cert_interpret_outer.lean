-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_interpret_outer
-- name    : Freiman.middleRepair_cert_interpret_outer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:51.361889+00:00
-- url     : https://prove2.me/theorems/4a5974c8-4e43-46fd-8ca2-eeabcfcdbf3a
-- title:
--   Report incoming-order repair: middleRepair_cert_interpret_outer
-- statement:
--   Read the two outer endpoint roles in the report coordinate. At width ties the child and corresponding virtual endpoint retain the same normalized-parent order; no physical/source endpoint equality is asserted.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem Freiman.middleRepair_cert_interpret_outer :
    (∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2))) → (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ (c : MiddleCore) (f : Fin 9), middleRepairCertDomain c f.val → middleRepairCertActualFamily c f.val → middleEssentialJ (middleCertRow f.val)=false → middleOuter c (middleRepairRowChildren c (middleCertRow f.val)) := by
  sorry
