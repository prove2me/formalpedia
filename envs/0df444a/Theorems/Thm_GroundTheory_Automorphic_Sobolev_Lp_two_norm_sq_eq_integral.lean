-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_Lp_two_norm_sq_eq_integral
-- name    : GroundTheory.Automorphic.Sobolev.Lp_two_norm_sq_eq_integral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:52.515422+00:00
-- url     : https://prove2.me/theorems/64e766a3-f9fe-45ff-b8f2-16c5fe2df3c7
-- title:
--   Sobolev: Lp two norm sq eq integral
-- statement:
--   The Sobolev construction uses the Lp two norm sq eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L336-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L336-L340

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

theorem GroundTheory.Automorphic.Sobolev.Lp_two_norm_sq_eq_integral (f : Lp F 2 (volume : Measure E)) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by sorry
