-- Prove2me | Theorems.Thm_GlobalTheory_graphClosure_isIso_fst_of_extension
-- name    : GlobalTheory.graphClosure.isIso_fst_of_extension
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:51.593164+00:00
-- url     : https://prove2.me/theorems/6ccad8a5-acda-431c-aa97-b3fe09993fed
-- title:
--   graph Closure: is Iso fst of extension
-- statement:
--   The graph Closure construction uses the is Iso fst of extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L580-L593
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L580-L593

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

theorem GlobalTheory.graphClosure.isIso_fst_of_extension [IsSchemeTheoreticallyDominant u] [IsSeparated f₂]
    (ψ : Z₁ ⟶ Z₂) (hψ : f₁ = ψ ≫ f₂) (hu : u ≫ ψ = φ) : IsIso (fst f₁ f₂ u φ h) := by sorry
