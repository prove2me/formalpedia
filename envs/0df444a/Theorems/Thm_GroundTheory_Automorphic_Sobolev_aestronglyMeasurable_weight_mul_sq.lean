-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_aestronglyMeasurable_weight_mul_sq
-- name    : GroundTheory.Automorphic.Sobolev.aestronglyMeasurable_weight_mul_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:55.441387+00:00
-- url     : https://prove2.me/theorems/40d3e43d-277b-4d2d-933a-597477faf2cc
-- title:
--   Sobolev: aestrongly Measurable weight mul sq
-- statement:
--   The Sobolev construction uses the aestrongly Measurable weight mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L94-L101

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

theorem GroundTheory.Automorphic.Sobolev.aestronglyMeasurable_weight_mul_sq {s : ℝ} (u : SobolevSpace E F s) (g : E → ℝ)
    (hg : Continuous g) :
    AEStronglyMeasurable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)
      (volume : Measure E) := by sorry
