-- Prove2me | Theorems.Thm_GlobalTheory_CharCutoff_sum_char
-- name    : GlobalTheory.CharCutoff.sum_char
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:56.582114+00:00
-- url     : https://prove2.me/theorems/143050a8-5e06-4f28-bdc1-499f35296cb1
-- title:
--   Char Cutoff: sum char
-- statement:
--   The Char Cutoff construction uses the sum char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsCutoffOfAddCharTranslationInvariantFunctio.lean#L45-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsCutoffOfAddCharTranslationInvariantFunctio.lean#L45-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsIntegralScaledBoxPiSupersetOfIsCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetIntegralScaledBoxPiCosetRepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralBoxInvariantEqMeasureRealMulSumRepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsCutoffOfAddCharTranslationInvariantFunctio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CharCutoff
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CharCutoff.sum_char {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s R : kˣ) (S : Finset (n → k)) (hS : ∀ b ∈ S, b ∈ box n (c * s⁻¹))
    (hU : ∀ a ∈ box n (c * s⁻¹), ∃! b, b ∈ S ∧ a - b ∈ box n (c * R⁻¹)) {y : n → k}
    (hy : y ∈ box n R) :
    ∑ b ∈ S, (ψ (b ⬝ᵥ y) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) y * S.card := by sorry
