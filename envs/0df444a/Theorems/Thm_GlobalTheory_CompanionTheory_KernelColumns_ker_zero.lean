-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_ker_zero
-- name    : GlobalTheory.CompanionTheory.KernelColumns.ker_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:54.915561+00:00
-- url     : https://prove2.me/theorems/e8c64ddb-136b-49e3-9563-93e4d4d2b37d
-- title:
--   Kernel Columns: ker zero
-- statement:
--   The Kernel Columns construction uses the ker zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L12-L13

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

theorem GlobalTheory.CompanionTheory.KernelColumns.ker_zero (X : Ctx) (x y : X.G) : ker X.Γ (0 : X.G → ℂ) x y = 0 := by sorry
