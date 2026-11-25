-- Prove2me | Theorems.Thm_GlobalTheory_graphClosure_opensRange_incl
-- name    : GlobalTheory.graphClosure.opensRange_incl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:52.14785+00:00
-- url     : https://prove2.me/theorems/5735593a-e8c0-4a6b-821b-232bed058e54
-- title:
--   graph Closure: opens Range incl
-- statement:
--   The graph Closure construction uses the opens Range incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L557-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L557-L559

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

theorem GlobalTheory.graphClosure.opensRange_incl [IsOpenImmersion u] [QuasiCompact u] [IsSeparated f₂] :
    (incl f₁ f₂ u φ h).opensRange = fst f₁ f₂ u φ h ⁻¹ᵁ u.opensRange := by sorry
