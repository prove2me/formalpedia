-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_inclusion_sub_eq
-- name    : GroundTheory.Automorphic.Sobolev.norm_inclusion_sub_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:11.548736+00:00
-- url     : https://prove2.me/theorems/d8bdad05-f0b1-4ee3-a4cb-de9fcd5c3429
-- title:
--   Sobolev: norm inclusion sub eq
-- statement:
--   The Sobolev construction uses the norm inclusion sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L257-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L257-L263

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
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

theorem GroundTheory.Automorphic.Sobolev.norm_inclusion_sub_eq {s r : ℝ} (h : r ≤ s) (v w : SobolevSpace E ℂ s) :
    ‖SobolevSpace.inclusion h v - SobolevSpace.inclusion h w‖ =
      ‖(𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h v)) : Lp ℂ 2 (volume : Measure E)) -
        𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h w))‖ := by sorry
