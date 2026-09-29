-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_source_case_11
-- name    : Freiman.lowerHistory_row2_source_case_11
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T00:52:35.171701+00:00
-- url     : https://prove2.me/theorems/493eaedd-7f51-4dc9-b1e7-6254996b1caa
-- title:
--   Freiman H5: necessary row-2 source alternatives, case 11
-- statement:
--   Let $p$ be one of the listed descriptors for row 2 and let $b$ be the base pair. Suppose that $b$ satisfies the original source events along $p$, including the base inequalities, the normalization at each stage, the selected choices, and the final row cuts. At least one of the displayed finite lists of bound indices then holds at the base coordinates:
--
--   $$\exists I\in\mathcal A_p\quad\forall i\in I,\quad B_i(r_b,s_b,q_b).$$
--
--   Here $B_i$ is the original indexed bound and $(r_b,s_b,q_b)$ are the two base ratios and the scale. The complete alternatives and descriptor list are specified in the formal statement. This supplies the necessary inequalities to the existing exact witness certificates in the row-2 argument for the H5 exception anchor.
-- source:
--   Freiman report, global_selection.tex and history_certificates.tex, appendix app:all-suffix-histories; original lowerHistory source-event definitions. Row-2 prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_row2_source_case_11 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[10],lowerHistoryPathsR[25],lowerHistoryPathsR[40],lowerHistoryPathsR[55],lowerHistoryPathsR[70],lowerHistoryPathsR[85]] →
  LowerHistorySourceEvents base p →
  ∃ bs ∈ ([[430,371,843,260,440,856,833,1176,274,851].map lowerHistoryBound] : List (List CertBound)), lowerHistoryAtBase base bs := by sorry
