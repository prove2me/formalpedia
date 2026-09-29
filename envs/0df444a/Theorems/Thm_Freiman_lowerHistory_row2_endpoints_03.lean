-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_endpoints_03
-- name    : Freiman.lowerHistory_row2_endpoints_03
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T01:15:04.452967+00:00
-- url     : https://prove2.me/theorems/bccb702b-bfa4-4be4-bee3-63e1d4ed5f2a
-- title:
--   Freiman H5: exact row-2 endpoint comparisons, case 03
-- statement:
--   For each listed row-2 descriptor $p$, the endpoint comparisons have exactly the displayed finite expansion. An item $(I,j)$ consists of the indexed conditions $B_i$ for $i\in I$, followed by the comparison whose bound is the complement of $B_j$. Thus the expansion specifies both the antecedent inequalities and the required endpoint comparison for every possible endpoint branch. The two endpoint shapes and their possible shortened endpoints are those of the original Freiman history construction. This finite identity supplies the exact comparison conditions used to certify the H5 row-2 prerequisite.
-- source:
--   Freiman report, global_selection.tex and history_certificates.tex, appendix app:all-suffix-histories; original lowerHistory source-event definitions. Row-2 prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_endpoints_03 : ∀ p : LowerHistoryPath, p ∈ [lowerHistoryPathsR[50],lowerHistoryPathsR[80]] → lowerHistoryEndpointComparisons p = [([834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1119))),
([834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1121))),
([283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1119))),
([283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1116)))] := by sorry
