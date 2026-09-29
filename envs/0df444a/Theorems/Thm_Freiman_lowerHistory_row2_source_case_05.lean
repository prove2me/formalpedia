-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_source_case_05
-- name    : Freiman.lowerHistory_row2_source_case_05
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T00:52:22.683397+00:00
-- url     : https://prove2.me/theorems/49752c7b-65aa-4b15-b13e-0d7c3f33c372
-- title:
--   Freiman H5: necessary row-2 source alternatives, case 05
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

theorem Freiman.lowerHistory_row2_source_case_05 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[4],lowerHistoryPathsR[19],lowerHistoryPathsR[34],lowerHistoryPathsR[49],lowerHistoryPathsR[64],lowerHistoryPathsR[79]] →
  LowerHistorySourceEvents base p →
  ∃ bs ∈ ([[1153,1146,371,843,260,440,856,420,416,781,711,191,711].map lowerHistoryBound,
[1153,267,821,772,1157,371,843,260,440,856,420,416,781,711,191,711].map lowerHistoryBound,
[275,876,1146,371,843,260,440,856,420,416,781,711,191,711].map lowerHistoryBound,
[275,876,267,821,772,1157,371,843,260,440,856,420,416,781,711,191,711].map lowerHistoryBound] : List (List CertBound)), lowerHistoryAtBase base bs := by sorry
