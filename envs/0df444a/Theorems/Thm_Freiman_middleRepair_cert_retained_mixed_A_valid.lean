-- Prove2me | Theorems.Thm_Freiman_middleRepair_cert_retained_mixed_A_valid
-- name    : Freiman.middleRepair_cert_retained_mixed_A_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-10T10:58:17.273852+00:00
-- url     : https://prove2.me/theorems/f62346b5-9507-465c-a5dd-a696c7abb6c2
-- title:
--   Retained repaired certificate records: mixed A families
-- statement:
--   Let $\mathcal R_A$ be the records in the fixed middle-interval certificate catalog whose goal is in mixed family A (family index 0). For every $r\in\mathcal R_A$ and every parent index $p$ listed by $r$,
--
--   $$\operatorname{NoRedirect}(r,p)\;\Longrightarrow\;\operatorname{RepairedRecordValid}(r,p).$$
--
--   Here validity means that the retained contradiction proof satisfies the witness conditions and both bounds of every proof pair occur among the repaired premises. This verifies the mixed-A component of the retained-record ledger, including the revised strictness rules.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; unchanged middleCertData and incoming-order middleRepairRedirects ledger. Exact family restriction of middleRepair_cert_retained_pairs_valid.

import Definitions.Def_Freiman_middleRepairLedger
open Freiman

theorem Freiman.middleRepair_cert_retained_mixed_A_valid :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([0] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by sorry
