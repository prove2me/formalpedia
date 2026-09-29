-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_interpret_uniform
-- name    : Freiman.middleRepair_cert_interpret_uniform
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:59.233418+00:00
-- url     : https://prove2.me/theorems/a8361e61-9560-4c0f-8e8a-870fa4f8a861
-- title:
--   Report incoming-order repair: middleRepair_cert_interpret_uniform
-- statement:
--   Use the uniform certificate comparison in its actual parity and the generic goodness criterion.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem Freiman.middleRepair_cert_interpret_uniform :
    (∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2))) → (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ c : MiddleCore, middleRegular c → (∃ f : Fin 11, 9≤f.val ∧ middleRepairCertDomain c f.val ∧ middleRepairCertActualFamily c f.val) → middleRepairGood c := by
  sorry
