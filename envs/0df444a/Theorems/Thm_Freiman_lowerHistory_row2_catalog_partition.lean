-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_catalog_partition
-- name    : Freiman.lowerHistory_row2_catalog_partition
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:44:08.593912+00:00
-- url     : https://prove2.me/theorems/6cf8b527-381e-4eed-a7fd-c1d9a062211b
-- title:
--   Freiman H5 row-2 catalogue partition
-- statement:
--   Project every original history descriptor onto its row number. The resulting list of 1,492 integers contains exactly 124 occurrences of row two, at the explicitly displayed indices. This finite integer identity is checked by reduction. A general list-index argument then associates any row-two descriptor with one of these indices. The original array concatenation and lookup identities identify the descriptor without comparing the full path records. Ninety descriptors come from the right catalogue and thirty-four from the initial catalogue. The two initial survivors satisfy the original survivor predicate; every other descriptor belongs to one of the thirty-two displayed groups. Thus the disjunction exhausts all original row-two descriptors.
--
--
--   The complete original descriptors and hypotheses are listed in the formal statement.
-- source:
--   Original Freiman lowerHistory catalogue, source events and endpoint semantics. Prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_catalog_partition : ∀ p ∈ lowerHistoryPaths.toList, p.row = 2 →
  lowerHistorySurvivor p ∨
  p ∈ [lowerHistoryPathsR[0],lowerHistoryPathsR[15],lowerHistoryPathsR[30],lowerHistoryPathsR[45],lowerHistoryPathsR[60],lowerHistoryPathsR[75]] ∨
  p ∈ [lowerHistoryPathsR[1],lowerHistoryPathsR[16],lowerHistoryPathsR[31],lowerHistoryPathsR[46],lowerHistoryPathsR[61],lowerHistoryPathsR[76]] ∨
  p ∈ [lowerHistoryPathsR[2],lowerHistoryPathsR[17],lowerHistoryPathsR[32],lowerHistoryPathsR[47],lowerHistoryPathsR[62],lowerHistoryPathsR[77]] ∨
  p ∈ [lowerHistoryPathsR[3],lowerHistoryPathsR[18],lowerHistoryPathsR[33],lowerHistoryPathsR[48],lowerHistoryPathsR[63],lowerHistoryPathsR[78]] ∨
  p ∈ [lowerHistoryPathsR[4],lowerHistoryPathsR[19],lowerHistoryPathsR[34],lowerHistoryPathsR[49],lowerHistoryPathsR[64],lowerHistoryPathsR[79]] ∨
  p ∈ [lowerHistoryPathsR[5],lowerHistoryPathsR[20],lowerHistoryPathsR[35],lowerHistoryPathsR[50],lowerHistoryPathsR[65],lowerHistoryPathsR[80]] ∨
  p ∈ [lowerHistoryPathsR[6],lowerHistoryPathsR[21],lowerHistoryPathsR[36],lowerHistoryPathsR[51],lowerHistoryPathsR[66],lowerHistoryPathsR[81]] ∨
  p ∈ [lowerHistoryPathsR[7],lowerHistoryPathsR[22],lowerHistoryPathsR[37],lowerHistoryPathsR[52],lowerHistoryPathsR[67],lowerHistoryPathsR[82]] ∨
  p ∈ [lowerHistoryPathsR[8],lowerHistoryPathsR[23],lowerHistoryPathsR[38],lowerHistoryPathsR[53],lowerHistoryPathsR[68],lowerHistoryPathsR[83]] ∨
  p ∈ [lowerHistoryPathsR[9],lowerHistoryPathsR[24],lowerHistoryPathsR[39],lowerHistoryPathsR[54],lowerHistoryPathsR[69],lowerHistoryPathsR[84]] ∨
  p ∈ [lowerHistoryPathsR[10],lowerHistoryPathsR[25],lowerHistoryPathsR[40],lowerHistoryPathsR[55],lowerHistoryPathsR[70],lowerHistoryPathsR[85]] ∨
  p ∈ [lowerHistoryPathsR[11],lowerHistoryPathsR[26],lowerHistoryPathsR[41],lowerHistoryPathsR[56],lowerHistoryPathsR[71],lowerHistoryPathsR[86]] ∨
  p ∈ [lowerHistoryPathsR[12],lowerHistoryPathsR[27],lowerHistoryPathsR[42],lowerHistoryPathsR[57],lowerHistoryPathsR[72],lowerHistoryPathsR[87]] ∨
  p ∈ [lowerHistoryPathsR[13],lowerHistoryPathsR[28],lowerHistoryPathsR[43],lowerHistoryPathsR[58],lowerHistoryPathsR[73],lowerHistoryPathsR[88]] ∨
  p ∈ [lowerHistoryPathsR[14],lowerHistoryPathsR[29],lowerHistoryPathsR[44],lowerHistoryPathsR[59],lowerHistoryPathsR[74],lowerHistoryPathsR[89]] ∨
  p ∈ [lowerHistoryPathsH[6]] ∨
  p ∈ [lowerHistoryPathsH[17],lowerHistoryPathsH[222]] ∨
  p ∈ [lowerHistoryPathsH[24],lowerHistoryPathsH[229]] ∨
  p ∈ [lowerHistoryPathsH[39]] ∨
  p ∈ [lowerHistoryPathsH[50],lowerHistoryPathsH[242]] ∨
  p ∈ [lowerHistoryPathsH[63],lowerHistoryPathsH[255]] ∨
  p ∈ [lowerHistoryPathsH[73],lowerHistoryPathsH[265]] ∨
  p ∈ [lowerHistoryPathsH[84],lowerHistoryPathsH[276]] ∨
  p ∈ [lowerHistoryPathsH[98],lowerHistoryPathsH[290]] ∨
  p ∈ [lowerHistoryPathsH[107],lowerHistoryPathsH[299]] ∨
  p ∈ [lowerHistoryPathsH[122],lowerHistoryPathsH[314]] ∨
  p ∈ [lowerHistoryPathsH[131],lowerHistoryPathsH[323]] ∨
  p ∈ [lowerHistoryPathsH[147],lowerHistoryPathsH[339]] ∨
  p ∈ [lowerHistoryPathsH[156],lowerHistoryPathsH[348]] ∨
  p ∈ [lowerHistoryPathsH[172],lowerHistoryPathsH[364]] ∨
  p ∈ [lowerHistoryPathsH[193],lowerHistoryPathsH[383]] ∨
  p ∈ [lowerHistoryPathsH[205],lowerHistoryPathsH[395]] := by sorry
