-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_normalizationMap_of_mono
-- name    : GlobalTheory.isPullback_normalizationMap_of_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:59:26.997473+00:00
-- url     : https://prove2.me/theorems/29b52baf-7f49-4c57-96e1-283ca39a832c
-- title:
--   Global Theory: is Pullback normalization Map of mono
-- statement:
--   The Global Theory construction uses the is Pullback normalization Map of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L443-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L443-L446

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

theorem GlobalTheory.isPullback_normalizationMap_of_mono [QuasiCompact f'] [QuasiSeparated f'] :
    IsPullback (normalizationMap f' f (𝟙 X) b (by simp [H])) f'.fromNormalization
      f.fromNormalization b := by sorry
