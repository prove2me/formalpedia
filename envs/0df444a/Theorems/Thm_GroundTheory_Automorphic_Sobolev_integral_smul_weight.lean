-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_integral_smul_weight
-- name    : GroundTheory.Automorphic.Sobolev.integral_smul_weight
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:21.29399+00:00
-- url     : https://prove2.me/theorems/36f7daf9-9f49-4493-a198-abe3cb2e467c
-- title:
--   Sobolev: integral smul weight
-- statement:
--   The Sobolev construction uses the integral smul weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L351-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L351-L357

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {m : E → ℂ} {C s t : ℝ}

theorem GroundTheory.Automorphic.Sobolev.integral_smul_weight (r : ℝ) (φ : 𝓢(E, ℂ)) (g : Lp F 2 (volume : Measure E)) :
    (g : 𝓢'(E, F)) (SchwartzMap.smulLeftCLM ℂ (weight r) φ) =
      ∫ ξ, φ ξ • (weight r ξ • g ξ) := by sorry
