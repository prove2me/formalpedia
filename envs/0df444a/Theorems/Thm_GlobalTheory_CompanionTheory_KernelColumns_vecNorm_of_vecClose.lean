-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_vecNorm_of_vecClose
-- name    : GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:24.893083+00:00
-- url     : https://prove2.me/theorems/f0c97026-1ec6-4c24-bcad-136b2d367239
-- title:
--   Kernel Columns: vec Norm of vec Close
-- statement:
--   The Kernel Columns construction uses the vec Norm of vec Close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L39-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L39-L57

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

theorem GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose : VecClose → VecNorm := by sorry
