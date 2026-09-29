-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_certificate_case_06
-- name    : Freiman.lowerHistory_row2_certificate_case_06
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:50:55.373597+00:00
-- url     : https://prove2.me/theorems/cb189314-ecc1-451c-86c4-f69cac4e1b7c
-- title:
--   Freiman H5 row-2 certified case 6
-- statement:
--   Let $b$ be a base pair and $p$ a descriptor in the displayed finite class. Write $\mathcal E(b,p)$ for its original source-event conditions, $R_p$ for its recorded rational rectangle, and $(r_b,s_b,q_b)$ for the two base ratios and scale.
--
--   Let $E_p$ be the original endpoint comparison list. Then
--
--   $$\mathcal E(b,p)\land(r_b,s_b)\in R_p\ \Longrightarrow\
--   \forall(C,g)\in E_p,\quad\left(\bigwedge_{c\in C}c(r_b,s_b,q_b)\right)\Rightarrow g(r_b,s_b,q_b).$$
--
--   Moreover, the descriptor is not initial and its row is not four. This establishes the comparisons needed to transfer the earlier anchor to the attained target.
-- source:
--   Original Freiman lowerHistory catalogue, source events and endpoint semantics. Prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_certificate_case_06 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[5],lowerHistoryPathsR[20],lowerHistoryPathsR[35],lowerHistoryPathsR[50],lowerHistoryPathsR[65],lowerHistoryPathsR[80]] →
  LowerHistorySourceEvents base p → certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) →
  p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by sorry
