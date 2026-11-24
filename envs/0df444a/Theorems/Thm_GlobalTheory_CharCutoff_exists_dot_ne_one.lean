-- Prove2me | Theorems.Thm_GlobalTheory_CharCutoff_exists_dot_ne_one
-- name    : GlobalTheory.CharCutoff.exists_dot_ne_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:08:27.000828+00:00
-- url     : https://prove2.me/theorems/3a31378e-45f3-47f5-8712-369a09ed918a
-- title:
--   Char Cutoff: exists dot ne one
-- statement:
--   The Char Cutoff construction uses the exists dot ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsCutoffOfAddCharTranslationInvariantFunctio.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsCutoffOfAddCharTranslationInvariantFunctio.lean#L29-L43

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

theorem GlobalTheory.CharCutoff.exists_dot_ne_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s : kˣ) {y : n → k} (hy : y ∉ box n s) : ∃ b ∈ box n (c * s⁻¹), ψ (b ⬝ᵥ y) ≠ 1 := by sorry
