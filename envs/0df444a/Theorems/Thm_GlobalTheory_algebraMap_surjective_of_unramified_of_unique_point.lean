-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_surjective_of_unramified_of_unique_point
-- name    : GlobalTheory.algebraMap_surjective_of_unramified_of_unique_point
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:48.864235+00:00
-- url     : https://prove2.me/theorems/52760110-d383-4b07-b0ed-c5b67fd67b0c
-- title:
--   Global Theory: algebra Map surjective of unramified of unique point
-- statement:
--   The Global Theory construction uses the algebra Map surjective of unramified of unique point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AlgebraMapSurjectiveOfUnramifiedOfUniquePoint.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AlgebraMapSurjectiveOfUnramifiedOfUniquePoint.lean#L7-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.algebraMap_surjective_of_unramified_of_unique_point (K A : Type) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.FormallyUnramified K A]
    (φ : A →ₐ[K] K) (hφ : ∀ ψ : A →ₐ[K] K, ψ = φ) : Function.Surjective (algebraMap K A) := by sorry
