-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CellSumProof_measurable_hits
-- name    : GlobalTheory.CompanionTheory.CellSumProof.measurable_hits
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:20.954784+00:00
-- url     : https://prove2.me/theorems/2c02a6ed-2420-492d-b7c7-0fd03da37168
-- title:
--   Cell Sum Proof: measurable hits
-- statement:
--   The Cell Sum Proof construction uses the measurable hits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CellSumOfCntBasic.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CellSumOfCntBasic.lean#L13-L17

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

theorem GlobalTheory.CompanionTheory.CellSumProof.measurable_hits (X : Ctx) {S : Set X.G} (hS : MeasurableSet S) :
    Measurable (hits X S) := by sorry
