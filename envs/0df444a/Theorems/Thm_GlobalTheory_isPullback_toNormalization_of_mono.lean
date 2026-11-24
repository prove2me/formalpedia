-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_toNormalization_of_mono
-- name    : GlobalTheory.isPullback_toNormalization_of_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:54.837976+00:00
-- url     : https://prove2.me/theorems/696c7262-9af7-4fae-8551-bfa303e7a7f0
-- title:
--   Global Theory: is Pullback to Normalization of mono
-- statement:
--   The Global Theory construction uses the is Pullback to Normalization of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L424-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L424-L426

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

theorem GlobalTheory.isPullback_toNormalization_of_mono [IsIntegralHom f'] :
    IsPullback f.toNormalization f' f.fromNormalization b := by sorry
