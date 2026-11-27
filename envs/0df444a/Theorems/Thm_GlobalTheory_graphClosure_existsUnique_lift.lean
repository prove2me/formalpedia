-- Prove2me | Theorems.Thm_GlobalTheory_graphClosure_existsUnique_lift
-- name    : GlobalTheory.graphClosure.existsUnique_lift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:40.437882+00:00
-- url     : https://prove2.me/theorems/a7802116-7195-41a3-a747-81bdcef58a66
-- title:
--   graph Closure: exists Unique lift
-- statement:
--   The graph Closure construction uses the exists Unique lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L484-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L484-L487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {S Z₁ Z₂ U T T' : Scheme.{u}} (f₁ : Z₁ ⟶ S) (f₂ : Z₂ ⟶ S) (u : U ⟶ Z₁) (φ : U ⟶ Z₂)
  (h : u ≫ f₁ = φ ≫ f₂)
open GlobalTheory.graphClosure
variable (t₁ : T ⟶ Z₁) (t₂ : T ⟶ Z₂) (ht : t₁ ≫ f₁ = t₂ ≫ f₂) (d : T' ⟶ T)
  [IsSchemeTheoreticallyDominant d] (w : T' ⟶ U) (h₁ : d ≫ t₁ = w ≫ u) (h₂ : d ≫ t₂ = w ≫ φ)
include ht h₁ h₂

theorem GlobalTheory.graphClosure.existsUnique_lift : ∃! l : T ⟶ graphClosure f₁ f₂ u φ h,
    l ≫ fst f₁ f₂ u φ h = t₁ ∧ l ≫ snd f₁ f₂ u φ h = t₂ := by sorry
