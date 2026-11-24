-- Prove2me | Theorems.Thm_GlobalTheory_SW_weil_parabolic
-- name    : GlobalTheory.SW.weil_parabolic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:57.136291+00:00
-- url     : https://prove2.me/theorems/f03d8d0b-b8d9-4362-9044-83ef265e0018
-- title:
--   SW: weil parabolic
-- statement:
--   The SW construction uses the weil parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionSiegelParabolicExplicit.lean#L440-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionSiegelParabolicExplicit.lean#L440-L481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.weil_parabolic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ), Even n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ → (∀ γ ∈ _root_.GlobalTheory.SW.UU E N, γ.toBlocks₂₁ = 0 → ∀ x, _root_.GlobalTheory.SW.weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) * _root_.GlobalTheory.SW.chiH Ψ (-(γ.toBlocks₁₂ * _root_.GlobalTheory.SW.ccT γ.toBlocks₁₁)) x * φ (x * γ.toBlocks₁₁)) ∧ ∀ γ ∈ _root_.GlobalTheory.SW.UU E N, ∀ γ' ∈ _root_.GlobalTheory.SW.UU E N, _root_.GlobalTheory.SW.botSpan γ = _root_.GlobalTheory.SW.botSpan γ' → ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z', _root_.GlobalTheory.SW.eisTerm Ψ γ φ Z z z' = _root_.GlobalTheory.SW.eisTerm Ψ γ' φ Z z z' := by sorry
