-- Prove2me | Theorems.Thm_GlobalTheory_flat_fromNormalization_comp
-- name    : GlobalTheory.flat_fromNormalization_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:45.4698+00:00
-- url     : https://prove2.me/theorems/2f9430d2-7a81-4d33-8e0c-454d5f722470
-- title:
--   Global Theory: flat from Normalization comp
-- statement:
--   The Global Theory construction uses the flat from Normalization comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L604-L608
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L604-L608

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

theorem GlobalTheory.flat_fromNormalization_comp [IsDedekindDomain R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (s : Y ⟶ Spec (.of R)) (c : X ⟶ Spec (.of K))
    (hc : f ≫ s = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    Flat (f.fromNormalization ≫ s) := by sorry
