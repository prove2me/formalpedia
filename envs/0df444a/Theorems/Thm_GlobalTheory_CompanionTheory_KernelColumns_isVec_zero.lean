-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_isVec_zero
-- name    : GlobalTheory.CompanionTheory.KernelColumns.isVec_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:47.158785+00:00
-- url     : https://prove2.me/theorems/1a78a42d-ee99-4e4c-9a27-df73d9996943
-- title:
--   Kernel Columns: is Vec zero
-- statement:
--   The Kernel Columns construction uses the is Vec zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecNormOfVecClose.lean#L15-L20

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

theorem GlobalTheory.CompanionTheory.KernelColumns.isVec_zero (X : Ctx) {ι : Type} [Fintype ι] (y : X.G) (j : ι) :
    X.IsVec (0 : Matrix ι ι (X.G → ℂ)) y j (0 : X.Hs ι) := by sorry
