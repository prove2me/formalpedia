-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_endpoints_01
-- name    : Freiman.lowerHistory_row2_endpoints_01
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T01:15:02.150881+00:00
-- url     : https://prove2.me/theorems/7d9dac67-c91b-4053-b13e-7e17e3dfcdc6
-- title:
--   Freiman H5: exact row-2 endpoint comparisons, case 01
-- statement:
--   For each listed row-2 descriptor $p$, the endpoint comparisons have exactly the displayed finite expansion. An item $(I,j)$ consists of the indexed conditions $B_i$ for $i\in I$, followed by the comparison whose bound is the complement of $B_j$. Thus the expansion specifies both the antecedent inequalities and the required endpoint comparison for every possible endpoint branch. The two endpoint shapes and their possible shortened endpoints are those of the original Freiman history construction. This finite identity supplies the exact comparison conditions used to certify the H5 row-2 prerequisite.
-- source:
--   Freiman report, global_selection.tex and history_certificates.tex, appendix app:all-suffix-histories; original lowerHistory source-event definitions. Row-2 prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_endpoints_01 : ∀ p : LowerHistoryPath, p ∈ [lowerHistoryPathsR[5],lowerHistoryPathsR[20],lowerHistoryPathsR[35],lowerHistoryPathsR[65]] → lowerHistoryEndpointComparisons p = [([836,1139,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([836,1139,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 880))),
([836,1139,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([836,1139,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 885))),
([836,259,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1179))),
([836,259,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1175))),
([836,259,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1179))),
([836,259,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1177))),
([284,429,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([284,429,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 880))),
([284,429,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([284,429,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 885))),
([284,819,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 895))),
([284,819,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 893))),
([284,819,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 895))),
([284,819,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 896)))] := by sorry
