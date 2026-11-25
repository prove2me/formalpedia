-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_fourierFun
-- name    : GroundTheory.Automorphic.Sobolev.integrable_fourierFun
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:34.148619+00:00
-- url     : https://prove2.me/theorems/34a76ab2-c8de-4e32-83a8-842f62f1fd97
-- title:
--   Sobolev: integrable fourier Fun
-- statement:
--   The Sobolev construction uses the integrable fourier Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L62-L66

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

theorem GroundTheory.Automorphic.Sobolev.integrable_fourierFun {s : ℝ} (hs : (Module.finrank ℝ E : ℝ) < 2 * s)
    (u : SobolevSpace E F s) : Integrable (fourierFun u) (volume : Measure E) := by sorry
