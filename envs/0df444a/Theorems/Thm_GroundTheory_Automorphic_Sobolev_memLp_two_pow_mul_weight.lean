-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_two_pow_mul_weight
-- name    : GroundTheory.Automorphic.Sobolev.memLp_two_pow_mul_weight
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:20.717157+00:00
-- url     : https://prove2.me/theorems/eb74ccb9-5a63-4712-81f6-4b9c130bcde7
-- title:
--   Sobolev: mem Lp two pow mul weight
-- statement:
--   The Sobolev construction uses the mem Lp two pow mul weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L15-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L15-L37

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

theorem GroundTheory.Automorphic.Sobolev.memLp_two_pow_mul_weight {s : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * (s - j)) :
    MemLp (fun ξ : E ↦ ‖ξ‖ ^ j * (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 (volume : Measure E) := by sorry
