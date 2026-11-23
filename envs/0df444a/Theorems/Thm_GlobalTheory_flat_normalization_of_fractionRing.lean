-- Prove2me | Theorems.Thm_GlobalTheory_flat_normalization_of_fractionRing
-- name    : GlobalTheory.flat_normalization_of_fractionRing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:47.672711+00:00
-- url     : https://prove2.me/theorems/9fe50ebd-75b8-4d78-8282-ddc00d6a5fe8
-- title:
--   Global Theory: flat normalization of fraction Ring
-- statement:
--   The Global Theory construction uses the flat normalization of fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L598-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L598-L602

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

theorem GlobalTheory.flat_normalization_of_fractionRing [IsDedekindDomain R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (p : f.normalization ⟶ Spec (.of R)) (c : X ⟶ Spec (.of K))
    (hc : f.toNormalization ≫ p = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) : Flat p := by sorry
