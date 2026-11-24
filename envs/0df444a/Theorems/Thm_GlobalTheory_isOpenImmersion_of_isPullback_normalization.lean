-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_of_isPullback_normalization
-- name    : GlobalTheory.isOpenImmersion_of_isPullback_normalization
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:08.24411+00:00
-- url     : https://prove2.me/theorems/069ce8d9-8608-4dda-8bf0-29645d713df5
-- title:
--   Global Theory: is Open Immersion of is Pullback normalization
-- statement:
--   The Global Theory construction uses the is Open Immersion of is Pullback normalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L400-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L400-L407

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

theorem GlobalTheory.isOpenImmersion_of_isPullback_normalization (h : IsPullback a f' f b)
    [PreservesNormalization b] [LocallyQuasiFinite f'] [LocallyOfFiniteType f'] [IsSeparated f']
    {N' : Scheme.{u}} {c : N' ⟶ f.normalization} {d : N' ⟶ Y'}
    (h' : IsPullback c d f.fromNormalization b) {e : X' ⟶ N'}
    (hc : e ≫ c = a ≫ f.toNormalization) (hd : e ≫ d = f') :
    IsOpenImmersion e ∧ IsSchemeTheoreticallyDominant e ∧ IsDominant e := by sorry
