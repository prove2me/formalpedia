-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_interpret_goodness
-- name    : Freiman.middleRepair_cert_interpret_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:11.320013+00:00
-- url     : https://prove2.me/theorems/e0c1ff8d-0836-4619-a9af-a2d36c36d0e1
-- title:
--   Report incoming-order repair: middleRepair_cert_interpret_goodness
-- statement:
--   Select the actual child normalization mode and apply the stored goodness-fork comparison in that mode; the independent goodness criterion supplies the automatic opposite cross inequality.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem Freiman.middleRepair_cert_interpret_goodness :
    (∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2))) → (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ (c : MiddleCore) (f : Fin 9), middleRepairCertDomain c f.val → middleRepairCertActualFamily c f.val → ∀ d ∈ middleRepairRowChildren c (middleCertRow f.val), middleRepairGood d := by
  sorry
