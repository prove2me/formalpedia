-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_bijective_of_unramified_of_unique_geometric_point
-- name    : GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:53.807696+00:00
-- url     : https://prove2.me/theorems/31123743-5949-5ae6-a161-ac441ad242ad
-- title:
--   Global Theory: algebra Map bijective of unramified of unique geometric point
-- statement:
--   The Global Theory construction uses the algebra Map bijective of unramified of unique geometric point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AlgebraMapSurjectiveOfUnramifiedOfUniquePoint.lean#L153-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AlgebraMapSurjectiveOfUnramifiedOfUniquePoint.lean#L153-L188

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
open scoped TensorProduct

theorem GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point :
    ∀ (R B : Type) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B] [Module.Finite R B]
      [Algebra.FormallyUnramified R B] (P : Set (Ideal R)),
      (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) →
      (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
        RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) →
      Function.Bijective (algebraMap R B) := by sorry
