-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_13
-- name    : Freiman.lowerHistory_row2_certificate_case_13
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:49:47.007345+00:00
-- url     : https://prove2.me/theorems/58c2b1f4-2a8d-4c4b-a5fa-c802f0aa7487
-- title:
--   Freiman H5 row-2 certified case 13
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

theorem Freiman.lowerHistory_row2_certificate_case_13 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[12],lowerHistoryPathsR[27],lowerHistoryPathsR[42],lowerHistoryPathsR[57],lowerHistoryPathsR[72],lowerHistoryPathsR[87]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  False := by sorry
