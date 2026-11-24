-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_enorm_sq_piLp_two
-- name    : GlobalTheory.CompanionTheory.KernelColumns.enorm_sq_piLp_two
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:44.309816+00:00
-- url     : https://prove2.me/theorems/3e0d5a4b-71cf-450e-a8eb-604178172122
-- title:
--   Kernel Columns: enorm sq pi Lp two
-- statement:
--   The Kernel Columns construction uses the enorm sq pi Lp two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecCloseOfKerBasicColSq.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecCloseOfKerBasicColSq.lean#L24-L32

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

theorem GlobalTheory.CompanionTheory.KernelColumns.enorm_sq_piLp_two {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : PiLp 2 E) :
    ‖f‖ₑ ^ 2 = ∑ l, ‖f l‖ₑ ^ 2 := by sorry
