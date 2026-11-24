-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_ker_sub_of_kerBasic
-- name    : GlobalTheory.CompanionTheory.KernelColumns.ker_sub_of_kerBasic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:10.114455+00:00
-- url     : https://prove2.me/theorems/6c9bd21d-7892-413d-869f-0d9954a444c9
-- title:
--   Kernel Columns: ker sub of ker Basic
-- statement:
--   The Kernel Columns construction uses the ker sub of ker Basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecCloseOfKerBasicColSq.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecCloseOfKerBasicColSq.lean#L12-L16

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecCloseOfKerBasicColSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns

theorem GlobalTheory.CompanionTheory.KernelColumns.ker_sub_of_kerBasic (hK : KerBasic) (X : Ctx) {φ φ' : X.G → ℂ} (h : Tst φ) (h' : Tst φ')
    (x y : X.G) :
    ker X.Γ (fun z => φ z - φ' z) x y = ker X.Γ φ x y - ker X.Γ φ' x y := by sorry
