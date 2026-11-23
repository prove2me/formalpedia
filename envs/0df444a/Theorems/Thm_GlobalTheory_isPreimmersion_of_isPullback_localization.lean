-- Prove2me | Theorems.Thm_GlobalTheory_isPreimmersion_of_isPullback_localization
-- name    : GlobalTheory.isPreimmersion_of_isPullback_localization
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:37.207279+00:00
-- url     : https://prove2.me/theorems/3694a5a3-b65a-4981-8ba4-2ad51884e9a4
-- title:
--   Global Theory: is Preimmersion of is Pullback localization
-- statement:
--   The Global Theory construction uses the is Preimmersion of is Pullback localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L469-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L469-L472

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
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (M : Submonoid R)
  [IsLocalization M R'] {Y Y' : Scheme.{u}} {b : Y' ⟶ Y} {t : Y' ⟶ Spec (.of R')}
  {s : Y ⟶ Spec (.of R)}
include M

theorem GlobalTheory.isPreimmersion_of_isPullback_localization
    (hb : IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    IsPreimmersion b := by sorry
