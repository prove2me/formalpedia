-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_ofSchwartz_eq
-- name    : GroundTheory.Automorphic.Sobolev.norm_ofSchwartz_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:49:44.248696+00:00
-- url     : https://prove2.me/theorems/0e59b1c4-6e22-58be-a0d2-6d19115b654a
-- title:
--   Sobolev: norm of Schwartz eq
-- statement:
--   The Sobolev construction uses the norm of Schwartz eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L112-L119

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.norm_ofSchwartz_eq (r : ℝ) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz r φ‖ =
      (eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume).toReal := by sorry
