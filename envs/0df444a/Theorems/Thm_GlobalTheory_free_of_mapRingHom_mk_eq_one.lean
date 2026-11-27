-- Prove2me | Theorems.Thm_GlobalTheory_free_of_mapRingHom_mk_eq_one
-- name    : GlobalTheory.free_of_mapRingHom_mk_eq_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:59.52905+00:00
-- url     : https://prove2.me/theorems/297f9ac7-db83-55b5-86b3-3fdc809ead95
-- title:
--   Global Theory: free of map Ring Hom mk eq one
-- statement:
--   The Global Theory construction uses the free of map Ring Hom mk eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UniqueFactorizationMonoidAddMonoidAlgebraOfFree.lean#L282-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UniqueFactorizationMonoidAddMonoidAlgebraOfFree.lean#L282-L288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing
open GlobalTheory
variable (A X : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [AddCommGroup X] [Module.Free ℤ X]
variable {X} (N : Type*) [AddCommGroup N] [Module (AddMonoidAlgebra A X) N]
  [Module.Invertible (AddMonoidAlgebra A X) N]

theorem GlobalTheory.free_of_mapRingHom_mk_eq_one (ε : AddMonoidAlgebra A X →ₐ[A] A)
    (h : Pic.mapRingHom (ε : AddMonoidAlgebra A X →+* A) (Pic.mk _ N) = 1) :
    Module.Free (AddMonoidAlgebra A X) N := by sorry
