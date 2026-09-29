-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_30
-- name    : Freiman.lowerHistory_row2_certificate_case_30
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:50:05.86772+00:00
-- url     : https://prove2.me/theorems/e9ed61b1-ae48-48ed-aef4-03f5b6aa77d9
-- title:
--   Freiman H5 row-2 certified case 30
-- statement:
--   Let $b$ be a base pair and $p$ a descriptor in the displayed finite class. Write $\mathcal E(b,p)$ for its original source-event conditions, $R_p$ for its recorded rational rectangle, and $(r_b,s_b,q_b)$ for the two base ratios and scale.
--
--   $$\mathcal E(b,p)\land(r_b,s_b)\in R_p\ \Longrightarrow\ \bot.$$
--
--   Consequently, no attained history satisfying the original source events and rectangle condition realizes a descriptor in this class. This eliminates the class in the exhaustive row-two target argument.
-- source:
--   Original Freiman lowerHistory catalogue, source events and endpoint semantics. Prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_certificate_case_30 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsH[172],lowerHistoryPathsH[364]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  False := by sorry
