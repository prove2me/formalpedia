-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_functions_of_isProper
-- name    : GlobalTheory.ProperFunctions.functions_of_isProper
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:15:55.5739+00:00
-- url     : https://prove2.me/theorems/d0890e0c-e7e0-4f7a-8539-1b7c94e74f0a
-- title:
--   Proper Functions: functions of is Proper
-- statement:
--   The Proper Functions construction uses the functions of is Proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L672-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L672-L703

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

theorem GlobalTheory.ProperFunctions.functions_of_isProper :
    (∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [IsProper p]
      [GeometricallyIntegral p],
        Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A],
          Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫
            (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)) ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{u})
      (p : X ⟶ Spec (.of R)) [IsProper p] [Flat p] [GeometricallyIntegral
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))],
        Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop)) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      [IsProper p] [Flat p] [GeometricallyIntegral p],
        Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) ∧
        ∀ (A : Type u) [CommRing A] [Algebra R A],
          Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫
            (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop)) := by sorry
