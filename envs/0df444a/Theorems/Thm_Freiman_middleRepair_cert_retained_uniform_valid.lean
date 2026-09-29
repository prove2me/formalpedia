-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_retained_uniform_valid
-- name    : Freiman.middleRepair_cert_retained_uniform_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-10T11:04:20.705522+00:00
-- url     : https://prove2.me/theorems/e54f4b61-f6f2-4cc4-bc36-3cdc554cafe4
-- title:
--   Retained repaired certificate records: uniform families
-- statement:
--   Let $\mathcal C$ be the fixed middle-interval certificate catalog and $F=[9, 10]$ the indicated group of row families. Every catalog record $r$ with goal family in $F$, and every listed parent $p$, has a valid retained repaired contradiction certificate whenever no ledger redirect applies:
--   $$\forall r\in\mathcal C.\mathrm{records},\ \mathrm{family}(r)\in F\ \Longrightarrow\ \forall p\in r.\mathrm{parents},\quad \mathrm{NoRedirect}(r,p)\Longrightarrow\mathrm{RepairRecordValid}(r,p).$$
--   Validity means that the adapted certificate has valid witness metadata and that each of its two bounds belongs to the repaired premises for that record and parent. This is the exact family restriction of middleRepair_cert_retained_pairs_valid, with the original catalog, ledger, and definitions preserved.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; unchanged middleCertData and incoming-order middleRepairRedirects ledger. Exact family restriction of middleRepair_cert_retained_pairs_valid.

import Definitions.Def_Freiman_middleRepairLedger
open Freiman

theorem Freiman.middleRepair_cert_retained_uniform_valid :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([9,10] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by sorry
