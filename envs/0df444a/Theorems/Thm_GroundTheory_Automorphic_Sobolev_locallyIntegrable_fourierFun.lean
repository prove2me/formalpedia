-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_locallyIntegrable_fourierFun
-- name    : GroundTheory.Automorphic.Sobolev.locallyIntegrable_fourierFun
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:56:10.721031+00:00
-- url     : https://prove2.me/theorems/f97466c8-6b34-410f-ad6d-e70c0cc18943
-- title:
--   Sobolev: locally Integrable fourier Fun
-- statement:
--   The Sobolev construction uses the locally Integrable fourier Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L146-L151

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
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

theorem GroundTheory.Automorphic.Sobolev.locallyIntegrable_fourierFun {s : ℝ} (u : SobolevSpace E F s) :
    LocallyIntegrable (fourierFun u) (volume : Measure E) := by sorry
