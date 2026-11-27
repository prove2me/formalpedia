-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_lift_toNormalization_of_isLocalization
-- name    : GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:26.337369+00:00
-- url     : https://prove2.me/theorems/7011cfb2-7d71-4ec3-b487-6418744648aa
-- title:
--   Global Theory: is Open Immersion lift to Normalization of is Localization
-- statement:
--   The Global Theory construction uses the is Open Immersion lift to Normalization of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L497-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L497-L510

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

theorem GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization
    (hb : IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    {X : Scheme.{u}} (f' : X ⟶ Y') [QuasiCompact f'] [LocallyQuasiFinite f']
    [LocallyOfFiniteType f'] [IsSeparated f'] (f : X ⟶ Y) (H : f = f' ≫ b) [QuasiCompact f]
    [QuasiSeparated f] :
    IsOpenImmersion (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsSchemeTheoreticallyDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) := by sorry
