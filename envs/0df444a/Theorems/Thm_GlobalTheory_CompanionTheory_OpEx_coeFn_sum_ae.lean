-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OpEx_coeFn_sum_ae
-- name    : GlobalTheory.CompanionTheory.OpEx.coeFn_sum_ae
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:36.8178+00:00
-- url     : https://prove2.me/theorems/1aec0001-5fb7-4296-af4a-ee066b46229f
-- title:
--   Op Ex: coe Fn sum ae
-- statement:
--   The Op Ex construction uses the coe Fn sum ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoeFnSumAe.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoeFnSumAe.lean#L12-L15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTailRest
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoeFnSumAe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OpEx
open PositivityTheory.Rg.BcB.E1

theorem GlobalTheory.CompanionTheory.OpEx.coeFn_sum_ae {α : Type} [MeasurableSpace α] {ν : Measure α} {ι : Type} (s : Finset ι)
    (g : ι → Lp ℂ 2 ν) :
    ((∑ j ∈ s, g j : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] fun x => ∑ j ∈ s, (g j : α → ℂ) x := by sorry
