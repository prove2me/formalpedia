-- Prove2me | Theorems.Thm_GlobalTheory_graphClosure_isProper_fst_comp
-- name    : GlobalTheory.graphClosure.isProper_fst_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:50.116404+00:00
-- url     : https://prove2.me/theorems/6dad5e73-3a30-4cd6-bd69-116c8e98ecdb
-- title:
--   graph Closure: is Proper fst comp
-- statement:
--   The graph Closure construction uses the is Proper fst comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L510-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L510-L511

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

theorem GlobalTheory.graphClosure.isProper_fst_comp [IsProper f₁] [IsProper f₂] : IsProper (fst f₁ f₂ u φ h ≫ f₁) := by sorry
