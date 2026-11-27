-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_normalizationMap_of_isIntegralHom_of_mono
-- name    : GlobalTheory.isPullback_normalizationMap_of_isIntegralHom_of_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:18.093412+00:00
-- url     : https://prove2.me/theorems/eff4d53b-1dd1-40ee-acb7-b0cf3218cad1
-- title:
--   Global Theory: is Pullback normalization Map of is Integral Hom of mono
-- statement:
--   The Global Theory construction uses the is Pullback normalization Map of is Integral Hom of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L450-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L450-L459

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

theorem GlobalTheory.isPullback_normalizationMap_of_isIntegralHom_of_mono {X T V Y : Scheme.{u}} (f₁ : X ⟶ T)
    (c : T ⟶ V) [IsIntegralHom c] (b : V ⟶ Y) [Mono b] [PreservesNormalization b] (f : X ⟶ Y)
    (H : f = f₁ ≫ c ≫ b) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f₁]
    [QuasiSeparated f₁] :
    IsPullback (normalizationMap f₁ f (𝟙 X) (c ≫ b) (by simp [H])) (f₁.fromNormalization ≫ c)
      f.fromNormalization b := by sorry
