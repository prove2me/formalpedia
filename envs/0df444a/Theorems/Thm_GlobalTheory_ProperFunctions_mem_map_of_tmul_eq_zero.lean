-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_of_tmul_eq_zero
-- name    : GlobalTheory.ProperFunctions.mem_map_of_tmul_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:49.290077+00:00
-- url     : https://prove2.me/theorems/9caac5c7-7ed0-416d-80f5-491bc2b2246d
-- title:
--   Proper Functions: mem map of tmul eq zero
-- statement:
--   The Proper Functions construction uses the mem map of tmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L13-L31

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

theorem GlobalTheory.ProperFunctions.mem_map_of_tmul_eq_zero {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [AddCommGroup M] [Module R M] (x : A) (m : M) (J : Ideal R)
    (hJ : ∀ r : R, r • m = 0 → r ∈ J) (h : x ⊗ₜ[R] m = 0) :
    x ∈ J.map (algebraMap R A) := by sorry
