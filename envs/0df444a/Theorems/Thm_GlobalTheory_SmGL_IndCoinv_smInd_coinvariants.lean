-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndCoinv_smInd_coinvariants
-- name    : GlobalTheory.SmGL.IndCoinv.smInd_coinvariants
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:31.819674+00:00
-- url     : https://prove2.me/theorems/72380a82-17a1-4b5b-8903-138ded8e5e10
-- title:
--   Ind Coinv: sm Ind coinvariants
-- statement:
--   The Ind Coinv construction uses the sm Ind coinvariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean#L65-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean#L65-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndCoinv
variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem GlobalTheory.SmGL.IndCoinv.smInd_coinvariants : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (P K : Subgroup G), IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) → (∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧ ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (U : Type) [AddCommGroup U] [Module ℂ U] (σ : Representation ℂ P X) (ρ : Representation ℂ P U), IsSmooth σ → ∀ (α : σ.IntertwiningMap ρ) (Γ : Type) (T : Γ → σ.IntertwiningMap σ), Function.Surjective α → (∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) → Function.Surjective (smIndMap α) ∧ ∀ f, smIndMap α f = 0 → f ∈ Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} := by sorry
