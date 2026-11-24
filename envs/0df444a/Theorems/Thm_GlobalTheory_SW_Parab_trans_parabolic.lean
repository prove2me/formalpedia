-- Prove2me | Theorems.Thm_GlobalTheory_SW_Parab_trans_parabolic
-- name    : GlobalTheory.SW.Parab.trans_parabolic
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:51.688218+00:00
-- url     : https://prove2.me/theorems/0245a074-8968-4cde-884e-572fcf07e0ee
-- title:
--   Parab: trans parabolic
-- statement:
--   The Parab construction uses the trans parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L172-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L172-L256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
open Matrix Complex
open scoped ComplexConjugate Real

theorem GlobalTheory.SW.Parab.trans_parabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ →
    σ.toBlocks₂₁ = 0 → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, _root_.GlobalTheory.SW.IsSB φ →
    _root_.GlobalTheory.SW.IsSB (ω φ) ∧ _root_.GlobalTheory.SW.TransS σ φ (ω φ) ∧
    ∀ φ', _root_.GlobalTheory.SW.IsSB φ' → _root_.GlobalTheory.SW.ip (ω φ) (ω φ') =
      _root_.GlobalTheory.SW.ip φ φ' := by sorry
