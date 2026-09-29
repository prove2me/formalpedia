-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_retained_equal_II_a_valid
-- name    : Freiman.middleRepair_cert_retained_equal_II_a_valid
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T10:50:53.103511+00:00
-- url     : https://prove2.me/theorems/b0035936-8a24-4fd9-8552-e31979990c0c
-- title:
--   Retained repaired certificate records: equal II a families
-- statement:
--   Let $\mathcal C$ be the fixed middle-interval certificate catalog and $F=[5]$ the row family $\mathrm{equalIIa}$ of the M2B table. Every catalog record $r$ whose goal lies in $F$, and every parent index $p$ listed by $r$, carries a valid retained repaired contradiction certificate whenever no ledger redirect applies:
--
--   $$\forall r\in\mathcal C.\mathrm{records},\ \mathrm{family}(r)\in F\ \Longrightarrow\ \forall p\in r.\mathrm{parents},\quad \mathrm{NoRedirect}(r,p)\Longrightarrow\mathrm{RepairRecordValid}(r,p).$$
--
--   Validity means that the adapted certificate has valid witness metadata and that each of its two bounds belongs to the repaired premises computed for that record and that parent. This is the exact family restriction of `middleRepair_cert_retained_pairs_valid` to the single row $\mathrm{equalIIa}$, with the original catalog, ledger, and definitions preserved.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; unchanged middleCertData and incoming-order middleRepairRedirects ledger. Exact family restriction of middleRepair_cert_retained_pairs_valid.

import Definitions.Def_Freiman_middleRepairLedger
open Freiman

theorem Freiman.middleRepair_cert_retained_equal_II_a_valid :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([5] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by sorry
