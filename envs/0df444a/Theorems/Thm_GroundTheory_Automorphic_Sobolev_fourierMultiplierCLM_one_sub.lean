-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierMultiplierCLM_one_sub
-- name    : GroundTheory.Automorphic.Sobolev.fourierMultiplierCLM_one_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:08.049846+00:00
-- url     : https://prove2.me/theorems/b5e29a7a-b242-4a49-94bf-dd604272db6b
-- title:
--   Sobolev: fourier Multiplier CLM one sub
-- statement:
--   The Sobolev construction uses the fourier Multiplier CLM one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L515-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L515-L526

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.fourierMultiplierCLM_one_sub {r : E → ℂ} (hr : r.HasTemperateGrowth) :
    fourierMultiplierCLM ℂ (fun ξ ↦ 1 - r ξ) =
      ContinuousLinearMap.id ℂ 𝓢'(E, ℂ) - fourierMultiplierCLM ℂ r := by sorry
