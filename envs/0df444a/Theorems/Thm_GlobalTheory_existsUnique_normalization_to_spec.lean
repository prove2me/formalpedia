-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_normalization_to_spec
-- name    : GlobalTheory.existsUnique_normalization_to_spec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:33.228802+00:00
-- url     : https://prove2.me/theorems/37269cf8-a675-4bd3-bf08-b994a90bf7be
-- title:
--   Global Theory: exists Unique normalization to spec
-- statement:
--   The Global Theory construction uses the exists Unique normalization to spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L610-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L610-L627

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  {R : Type u} [CommRing R]

theorem GlobalTheory.existsUnique_normalization_to_spec [IsDedekindDomain R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] {R₀ : Type u} [CommRing R₀] [Algebra R₀ R]
    [Algebra.IsIntegral R₀ R] (s : Y ⟶ Spec (.of R₀)) (c : X ⟶ Spec (.of K))
    (hc : f ≫ s = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) :
    (∃! p : f.normalization ⟶ Spec (.of R),
      f.toNormalization ≫ p = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
    ∀ p : f.normalization ⟶ Spec (.of R),
      f.toNormalization ≫ p = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) →
        Flat p ∧ p ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ R)) = f.fromNormalization ≫ s := by sorry
