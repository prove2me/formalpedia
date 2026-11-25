-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_pow_mul_norm_fourierFun
-- name    : GroundTheory.Automorphic.Sobolev.integrable_pow_mul_norm_fourierFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:53.188015+00:00
-- url     : https://prove2.me/theorems/72f94cc0-a79e-491d-82db-ec7bbb60e67b
-- title:
--   Sobolev: integrable pow mul norm fourier Fun
-- statement:
--   The Sobolev construction uses the integrable pow mul norm fourier Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L51-L60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem GroundTheory.Automorphic.Sobolev.integrable_pow_mul_norm_fourierFun {s : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * (s - j)) (u : SobolevSpace E F s) :
    Integrable (fun ξ : E ↦ ‖ξ‖ ^ j * ‖fourierFun u ξ‖) (volume : Measure E) := by sorry
