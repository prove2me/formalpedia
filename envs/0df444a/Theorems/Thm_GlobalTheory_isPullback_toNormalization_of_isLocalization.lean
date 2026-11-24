-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_toNormalization_of_isLocalization
-- name    : GlobalTheory.isPullback_toNormalization_of_isLocalization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:48.362801+00:00
-- url     : https://prove2.me/theorems/764c876b-ceae-4211-a67a-b3c955b969a6
-- title:
--   Global Theory: is Pullback to Normalization of is Localization
-- statement:
--   The Global Theory construction uses the is Pullback to Normalization of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L486-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L486-L493

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

theorem GlobalTheory.isPullback_toNormalization_of_isLocalization
    (hb : IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    {X V : Scheme.{u}} (f' : X ⟶ V) [IsIntegralHom f'] (i : V ⟶ Y') [IsOpenImmersion i]
    (f : X ⟶ Y) (H : f = f' ≫ i ≫ b) [QuasiCompact f] [QuasiSeparated f] :
    IsPullback f.toNormalization f' f.fromNormalization (i ≫ b) := by sorry
