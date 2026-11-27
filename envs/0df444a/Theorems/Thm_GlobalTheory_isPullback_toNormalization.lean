-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_toNormalization
-- name    : GlobalTheory.isPullback_toNormalization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:41.83003+00:00
-- url     : https://prove2.me/theorems/6f117143-7dc3-4683-aad7-28aede35c6f2
-- title:
--   Global Theory: is Pullback to Normalization
-- statement:
--   The Global Theory construction uses the is Pullback to Normalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L356-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L356-L358

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
variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']

theorem GlobalTheory.isPullback_toNormalization (h : IsPullback a f' f b) [PreservesNormalization b] :
    IsPullback a f'.toNormalization f.toNormalization (normalizationMap f' f a b h.w) := by sorry
