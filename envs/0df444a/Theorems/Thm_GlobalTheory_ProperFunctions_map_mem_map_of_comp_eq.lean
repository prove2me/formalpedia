-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_map_mem_map_of_comp_eq
-- name    : GlobalTheory.ProperFunctions.map_mem_map_of_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:42.636804+00:00
-- url     : https://prove2.me/theorems/2f90caaf-abb2-4fb4-a78c-4cc2ca22c195
-- title:
--   Proper Functions: map mem map of comp eq
-- statement:
--   The Proper Functions construction uses the map mem map of comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L188-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.map_mem_map_of_comp_eq {R A B : CommRingCat.{u}} {φ : R ⟶ A} {ψ : A ⟶ B} {χ : R ⟶ B}
    (h : φ ≫ ψ = χ) {I : Ideal R} {x : A} (hx : x ∈ I.map φ.hom) : ψ x ∈ I.map χ.hom := by sorry
