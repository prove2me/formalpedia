-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_surjective_appTop_of_forall_finiteType
-- name    : GlobalTheory.ProperFunctions.surjective_appTop_of_forall_finiteType
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:22.292607+00:00
-- url     : https://prove2.me/theorems/183399e8-62f1-47a2-af1c-1d5a02eeb1d1
-- title:
--   Proper Functions: surjective app Top of forall finite Type
-- statement:
--   The Proper Functions construction uses the surjective app Top of forall finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L532-L623
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L532-L623

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
variable {X Y S T : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.surjective_appTop_of_forall_finiteType {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {p : X ⟶ Spec (.of R)} [QuasiCompact p] [QuasiSeparated p]
    (h : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Function.Surjective
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    {g : Y ⟶ X} {q : Y ⟶ Spec (.of A)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Function.Surjective q.appTop := by sorry
