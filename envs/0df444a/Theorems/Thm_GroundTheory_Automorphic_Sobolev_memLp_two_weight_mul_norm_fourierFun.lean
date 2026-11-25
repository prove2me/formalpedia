-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_two_weight_mul_norm_fourierFun
-- name    : GroundTheory.Automorphic.Sobolev.memLp_two_weight_mul_norm_fourierFun
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:58.849984+00:00
-- url     : https://prove2.me/theorems/d94d761a-3a9f-4071-817c-b1ab702d5df6
-- title:
--   Sobolev: mem Lp two weight mul norm fourier Fun
-- statement:
--   The Sobolev construction uses the mem Lp two weight mul norm fourier Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L39-L49

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

theorem GroundTheory.Automorphic.Sobolev.memLp_two_weight_mul_norm_fourierFun {s : ℝ} (u : SobolevSpace E F s) :
    MemLp (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖fourierFun u ξ‖) 2 (volume : Measure E) := by sorry
