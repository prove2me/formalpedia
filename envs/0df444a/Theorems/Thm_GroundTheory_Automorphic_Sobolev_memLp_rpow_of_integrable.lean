-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_rpow_of_integrable
-- name    : GroundTheory.Automorphic.Sobolev.memLp_rpow_of_integrable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:15.670675+00:00
-- url     : https://prove2.me/theorems/71242eaa-cea7-4aff-ae73-f3e6e54a8882
-- title:
--   Sobolev: mem Lp rpow of integrable
-- statement:
--   The Sobolev construction uses the mem Lp rpow of integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L62-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L62-L75

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
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

theorem GroundTheory.Automorphic.Sobolev.memLp_rpow_of_integrable {A : E → ℝ} (hA : Integrable A (volume : Measure E))
    (h0 : ∀ ξ, 0 ≤ A ξ) {a : ℝ} (ha : 0 < a) :
    MemLp (fun ξ ↦ A ξ ^ a) (ENNReal.ofReal (1 / a)) (volume : Measure E) := by sorry
