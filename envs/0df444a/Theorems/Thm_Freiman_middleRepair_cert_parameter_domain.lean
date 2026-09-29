-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_parameter_domain
-- name    : Freiman.middleRepair_cert_parameter_domain
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:32:41.775159+00:00
-- url     : https://prove2.me/theorems/b33d308b-d576-4486-90de-de61dc9f4b3d
-- title:
--   Report incoming-order repair: middleRepair_cert_parameter_domain
-- statement:
--   The actual normalized continuant ratios lie in the closed source rectangle and the scale q is positive.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem Freiman.middleRepair_cert_parameter_domain :
    ∀ c : MiddleCore, middleRegular c → certRectangleMem middleCertRectangle (middleParameter (middleNormalized c).left) (middleParameter (middleNormalized c).right) ∧ 0 < middleQ c := by
  sorry
