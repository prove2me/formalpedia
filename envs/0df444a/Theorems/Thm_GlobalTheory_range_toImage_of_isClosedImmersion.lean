-- Prove2me | Theorems.Thm_GlobalTheory_range_toImage_of_isClosedImmersion
-- name    : GlobalTheory.range_toImage_of_isClosedImmersion
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:50:03.905519+00:00
-- url     : https://prove2.me/theorems/09cd9e29-cb2f-44b5-a992-3be7daca8b16
-- title:
--   Global Theory: range to Image of is Closed Immersion
-- statement:
--   The Global Theory construction uses the range to Image of is Closed Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L321-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L321-L326

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
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)

theorem GlobalTheory.range_toImage_of_isClosedImmersion {P' : Scheme.{u}} (c : W ⟶ P') (u : P' ⟶ P)
    [IsClosedImmersion c] [Flat u] [Mono u] (h : c ≫ u = j) [QuasiCompact j] :
    Set.range j.toImage = j.imageι ⁻¹' Set.range u := by sorry
