-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CellSumProof_cellSum_of_cntBasic
-- name    : GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:20.059484+00:00
-- url     : https://prove2.me/theorems/f6aef17e-888b-450f-a08a-11b290e495a5
-- title:
--   Cell Sum Proof: cell Sum of cnt Basic
-- statement:
--   The Cell Sum Proof construction uses the cell Sum of cnt Basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CellSumOfCntBasic.lean#L77-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CellSumOfCntBasic.lean#L77-L77

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CellSumOfCntBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CellSumProof

theorem GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic : CntBasic → CellSum := by sorry
