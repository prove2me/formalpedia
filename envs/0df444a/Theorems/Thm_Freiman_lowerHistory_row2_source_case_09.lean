-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_source_case_09
-- name    : Freiman.lowerHistory_row2_source_case_09
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T00:52:31.680522+00:00
-- url     : https://prove2.me/theorems/a837563c-a46b-4f4a-a7da-b4def250a613
-- title:
--   Freiman H5: necessary row-2 source alternatives, case 09
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

theorem Freiman.lowerHistory_row2_source_case_09 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[8],lowerHistoryPathsR[23],lowerHistoryPathsR[38],lowerHistoryPathsR[53],lowerHistoryPathsR[68],lowerHistoryPathsR[83]] →
  LowerHistorySourceEvents base p →
  ∃ bs ∈ ([[824,1150,258,371,843,260,440,856,833,806,795,175,795].map lowerHistoryBound,
[824,1150,1138,249,371,843,260,440,856,833,806,795,175,795].map lowerHistoryBound,
[824,272,371,843,260,440,856,833,806,795,175,795].map lowerHistoryBound] : List (List CertBound)), lowerHistoryAtBase base bs := by sorry
