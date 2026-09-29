-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_source_case_14
-- name    : Freiman.lowerHistory_row2_source_case_14
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T00:53:02.201487+00:00
-- url     : https://prove2.me/theorems/ca386947-256e-459a-a236-88fb4b8a222d
-- title:
--   Freiman H5: necessary row-2 source alternatives, case 14
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

theorem Freiman.lowerHistory_row2_source_case_14 : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsR[13],lowerHistoryPathsR[28],lowerHistoryPathsR[43],lowerHistoryPathsR[58],lowerHistoryPathsR[73],lowerHistoryPathsR[88]] →
  LowerHistorySourceEvents base p →
  ∃ bs ∈ ([[371,843,260,440,856,833,254,810,769,220,769].map lowerHistoryBound] : List (List CertBound)), lowerHistoryAtBase base bs := by sorry
