-- Prove2me | Theorems.Thm_GlobalTheory_Phase_transS_intertwines
-- name    : GlobalTheory.Phase.transS_intertwines
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:17.627804+00:00
-- url     : https://prove2.me/theorems/c602c725-b3af-4df5-9ec1-6027a6dfa4cb
-- title:
--   Phase: trans S intertwines
-- statement:
--   The Phase construction uses the trans S intertwines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TransSIntertwines.lean#L456-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TransSIntertwines.lean#L456-L479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSIntertwines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase GlobalTheory.SiegelAction
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase
open Inter
open Matrix Complex
open scoped ComplexConjugate Real
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.Phase.transS_intertwines : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∃ T : (Matrix κ ι ℚ × Matrix κ ι ℚ) ≃+ (Matrix κ ι ℚ × Matrix κ ι ℚ), (∀ y y', _root_.GlobalTheory.Phase.om (T y) (T y') = _root_.GlobalTheory.Phase.om y y') ∧ ∀ φ ψ : Matrix κ ι ℚ → ℂ, _root_.GlobalTheory.SW.IsSB φ → _root_.GlobalTheory.SW.IsSB ψ → _root_.GlobalTheory.SW.TransS σ φ ψ → ∀ y, _root_.GlobalTheory.SW.TransS σ (_root_.GlobalTheory.SW.heisS y.1 y.2 φ) (_root_.GlobalTheory.SW.heisS (T y).1 (T y).2 ψ) := by sorry
