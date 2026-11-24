-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_tst_zero
-- name    : GlobalTheory.CompanionTheory.KernelColumns.tst_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:08.16196+00:00
-- url     : https://prove2.me/theorems/e4e588e8-8e91-4677-9456-4bb3032ee7a4
-- title:
--   Kernel Columns: tst zero
-- statement:
--   The Kernel Columns construction uses the tst zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L22-L23

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecNormOfVecClose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns

theorem GlobalTheory.CompanionTheory.KernelColumns.tst_zero (X : Ctx) : Tst (0 : X.G → ℂ) := by sorry
