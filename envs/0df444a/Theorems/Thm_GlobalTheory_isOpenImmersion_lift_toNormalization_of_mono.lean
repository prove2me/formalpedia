-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_lift_toNormalization_of_mono
-- name    : GlobalTheory.isOpenImmersion_lift_toNormalization_of_mono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:54.756455+00:00
-- url     : https://prove2.me/theorems/7b02841c-fe9d-4ff1-a979-fe3ed2fd3025
-- title:
--   Global Theory: is Open Immersion lift to Normalization of mono
-- statement:
--   The Global Theory construction uses the is Open Immersion lift to Normalization of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L430-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L430-L439

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
variable {X Y V : Scheme.{u}} (f' : X ⟶ V) (b : V ⟶ Y) [Mono b] (f : X ⟶ Y) (H : f = f' ≫ b)
variable [QuasiCompact f] [QuasiSeparated f] [PreservesNormalization b]
include H

theorem GlobalTheory.isOpenImmersion_lift_toNormalization_of_mono [QuasiCompact f'] [LocallyQuasiFinite f']
    [LocallyOfFiniteType f'] [IsSeparated f'] :
    IsOpenImmersion (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsSchemeTheoreticallyDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) := by sorry
