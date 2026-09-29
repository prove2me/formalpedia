-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_source_case_24
-- name    : Freiman.lowerHistory_row2_source_case_24
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T01:03:18.513336+00:00
-- url     : https://prove2.me/theorems/73462525-e589-430b-97ca-977172f023c9
-- title:
--   Freiman H5: necessary row-2 source alternatives, case 24
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
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_source_case_24 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsH[98],lowerHistoryPathsH[290]] →
  LowerHistorySourceEvents base p →
  ∃ bs ∈ ([[1052,1008,371,843,433,1162,839,447,304,305,452,463,120,463].map lowerHistoryBound] : List (List CertBound)), lowerHistoryAtBase base bs := by sorry
