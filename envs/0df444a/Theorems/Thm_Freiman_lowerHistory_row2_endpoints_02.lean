-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_endpoints_02
-- name    : Freiman.lowerHistory_row2_endpoints_02
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T01:14:50.157319+00:00
-- url     : https://prove2.me/theorems/8a2a7ee7-a9b2-4128-a3b5-d73f4f11d4e6
-- title:
--   Freiman H5: exact row-2 endpoint comparisons, case 02
-- statement:
--   For each listed row-2 descriptor $p$, the endpoint comparisons have exactly the displayed finite expansion. An item $(I,j)$ consists of the indexed conditions $B_i$ for $i\in I$, followed by the comparison whose bound is the complement of $B_j$. Thus the expansion specifies both the antecedent inequalities and the required endpoint comparison for every possible endpoint branch. The two endpoint shapes and their possible shortened endpoints are those of the original Freiman history construction. This finite identity supplies the exact comparison conditions used to certify the H5 row-2 prerequisite.
-- source:
--   Freiman report, global_selection.tex and history_certificates.tex, appendix app:all-suffix-histories; original lowerHistory source-event definitions. Row-2 prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_endpoints_02 : ∀ p : LowerHistoryPath, p ∈ [lowerHistoryPathsR[7],lowerHistoryPathsR[22],lowerHistoryPathsR[37],lowerHistoryPathsR[67]] → lowerHistoryEndpointComparisons p = [([836,1139,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([836,1139,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 887))),
([836,1139,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([836,1139,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 890))),
([836,259,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1169))),
([836,259,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1167))),
([836,259,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1169))),
([836,259,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1166))),
([284,429,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([284,429,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 887))),
([284,429,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([284,429,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 890))),
([284,819,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 901))),
([284,819,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 900))),
([284,819,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 901))),
([284,819,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 902)))] := by sorry
