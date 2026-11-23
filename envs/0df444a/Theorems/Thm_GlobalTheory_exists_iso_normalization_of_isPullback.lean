-- Prove2me | Theorems.Thm_GlobalTheory_exists_iso_normalization_of_isPullback
-- name    : GlobalTheory.exists_iso_normalization_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:49.722434+00:00
-- url     : https://prove2.me/theorems/256498df-f265-45ad-948e-d3f8eed664f5
-- title:
--   Global Theory: exists iso normalization of is Pullback
-- statement:
--   The Global Theory construction uses the exists iso normalization of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L385-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L385-L392

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

theorem GlobalTheory.exists_iso_normalization_of_isPullback (h : IsPullback a f' f b) [PreservesNormalization b]
    {N' : Scheme.{u}} {c : N' ⟶ f.normalization} {d : N' ⟶ Y'}
    (h' : IsPullback c d f.fromNormalization b) {e : X' ⟶ N'}
    (hc : e ≫ c = a ≫ f.toNormalization) (hd : e ≫ d = f') :
    ∃ i : f'.normalization ≅ N', f'.toNormalization ≫ i.hom = e ∧
      i.hom ≫ d = f'.fromNormalization ∧ i.hom ≫ c = normalizationMap f' f a b h.w := by sorry
