-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_of_mul_mem_map
-- name    : GlobalTheory.ProperFunctions.mem_map_of_mul_mem_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:18.52156+00:00
-- url     : https://prove2.me/theorems/48517d9b-1086-4a71-94b5-2709fa829422
-- title:
--   Proper Functions: mem map of mul mem map
-- statement:
--   The Proper Functions construction uses the mem map of mul mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L33-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L33-L58

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

theorem GlobalTheory.ProperFunctions.mem_map_of_mul_mem_map {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (hφ : φ.Flat) (I J : Ideal R) (a : R) (hJ : ∀ r : R, r * a ∈ I → r ∈ J) (x : A)
    (h : φ a * x ∈ I.map φ) : x ∈ J.map φ := by sorry
