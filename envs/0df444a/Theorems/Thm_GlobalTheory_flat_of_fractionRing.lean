-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_fractionRing
-- name    : GlobalTheory.flat_of_fractionRing
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:50.663747+00:00
-- url     : https://prove2.me/theorems/17af6bb8-2567-45ff-ac8e-515ab5e54149
-- title:
--   Global Theory: flat of fraction Ring
-- statement:
--   The Global Theory construction uses the flat of fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L592-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L592-L596

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

theorem GlobalTheory.flat_of_fractionRing [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (c : X ⟶ Spec (.of K)) : Flat (c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) := by sorry
