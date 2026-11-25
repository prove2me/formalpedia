-- Prove2me | Theorems.Thm_GlobalTheory_graphClosure_flat_of_valuationRing
-- name    : GlobalTheory.graphClosure.flat_of_valuationRing
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:43.809623+00:00
-- url     : https://prove2.me/theorems/69d045fc-cf1a-5afe-a837-3284b1824fb3
-- title:
--   graph Closure: flat of valuation Ring
-- statement:
--   The graph Closure construction uses the flat of valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L610-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L610-L615

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

theorem GlobalTheory.graphClosure.flat_of_valuationRing {O : CommRingCat.{u}} [IsDomain O] [ValuationRing O]
    (f₁ : Z₁ ⟶ Spec O) (f₂ : Z₂ ⟶ Spec O) (u : U ⟶ Z₁) (φ : U ⟶ Z₂) (h : u ≫ f₁ = φ ≫ f₂)
    [QuasiCompact u] [QuasiSeparated f₂] [Flat (u ≫ f₁)] :
    Flat (graphClosure.fst f₁ f₂ u φ h ≫ f₁) := by sorry
