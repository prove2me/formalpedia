-- Prove2me | Theorems.Thm_GlobalTheory_graphClosure_range_incl
-- name    : GlobalTheory.graphClosure.range_incl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:05.614739+00:00
-- url     : https://prove2.me/theorems/cb293b15-376a-4aa6-a9b7-0c3ef4dae853
-- title:
--   graph Closure: range incl
-- statement:
--   The graph Closure construction uses the range incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L551-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L551-L555

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

theorem GlobalTheory.graphClosure.range_incl [Flat u] [Mono u] [QuasiCompact u] [IsSeparated f₂] :
    Set.range (incl f₁ f₂ u φ h) = fst f₁ f₂ u φ h ⁻¹' Set.range u := by sorry
