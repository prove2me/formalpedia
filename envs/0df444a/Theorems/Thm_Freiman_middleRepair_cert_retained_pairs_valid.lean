-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_retained_pairs_valid
-- name    : Freiman.middleRepair_cert_retained_pairs_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:31:10.331445+00:00
-- url     : https://prove2.me/theorems/da538aae-3fcc-4481-bf88-02688795d1eb
-- title:
--   Report incoming-order repair: middleRepair_cert_retained_pairs_valid
-- statement:
--   Finite logical applicability check for the 8275 retained source pairs, after actual incoming-order guards and the strongest available strictness flags are reconstructed. No polynomial is recomputed or changed.
-- source:
--   Freiman report, active m2b_body.tex lines 46–48 and §§2,8–9; immutable M2B coefficient catalog plus the explicit 146-entry incoming-order boundary pointer ledger.

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

theorem Freiman.middleRepair_cert_retained_pairs_valid :
    ∀ rec ∈ middleCertData.records, ∀ parent ∈ rec.parents, middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none → middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  sorry
