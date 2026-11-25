-- Prove2me | Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
-- name    : GlobalTheory.SW.unitary_act_halfSpace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:27.991943+00:00
-- url     : https://prove2.me/theorems/b22a3bb0-5150-4876-adf9-403d4ddee6c0
-- title:
--   SW: unitary act half Space
-- statement:
--   The SW construction uses the unitary act half Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L221-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L221-L263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
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
open GlobalTheory.SW.HAct

theorem GlobalTheory.SW.unitary_act_halfSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (N : ℕ) (γ : M2 E N), γ ∈ UU E N → (IsUnit γ.det ∧ γ⁻¹ ∈ UU E N ∧ ccT γ ∈ UU E N ∧ γ⁻¹ = -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) ∧ ∀ γ' ∈ UU E N, γ' * γ ∈ UU E N) ∧ ∀ Z ∈ Hn Ψ N, (∀ τ, (hDen Ψ γ Z τ).det ≠ 0 ∧ (hDen' Ψ γ Z τ).det * τ.1 γ.det = (hDen Ψ γ Z τ).det ∧ ‖τ.1 γ.det‖ = 1 ∧ (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ)) ∧ hAct Ψ γ Z ∈ Hn Ψ N ∧ detIm (hAct Ψ γ Z) * ∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2 = detIm Z ∧ ∀ γ' ∈ UU E N, hAct Ψ (γ' * γ) Z = hAct Ψ γ' (hAct Ψ γ Z) ∧ (∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ) ∧ ∀ τ, hDen' Ψ (γ' * γ) Z τ = hDen' Ψ γ Z τ * hDen' Ψ γ' (hAct Ψ γ Z) τ := by sorry
