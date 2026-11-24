-- Prove2me | Theorems.Thm_GlobalTheory_graphClosure_exists_extension_of_isIso_fst
-- name    : GlobalTheory.graphClosure.exists_extension_of_isIso_fst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:00.785221+00:00
-- url     : https://prove2.me/theorems/b1f76ef5-d0b4-4394-befd-bdd797e19d68
-- title:
--   graph Closure: exists extension of is Iso fst
-- statement:
--   The graph Closure construction uses the exists extension of is Iso fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L595-L599
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L595-L599

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

theorem GlobalTheory.graphClosure.exists_extension_of_isIso_fst [IsIso (fst f₁ f₂ u φ h)] :
    ∃ ψ : Z₁ ⟶ Z₂, f₁ = ψ ≫ f₂ ∧ u ≫ ψ = φ := by sorry
