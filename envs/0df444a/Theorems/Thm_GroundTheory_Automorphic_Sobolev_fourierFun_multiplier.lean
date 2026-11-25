-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_multiplier
-- name    : GroundTheory.Automorphic.Sobolev.fourierFun_multiplier
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:41.676117+00:00
-- url     : https://prove2.me/theorems/e9284905-d720-48a5-aa71-26b3e4f6510d
-- title:
--   Sobolev: fourier Fun multiplier
-- statement:
--   The Sobolev construction uses the fourier Fun multiplier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L26-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L26-L50

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
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

theorem GroundTheory.Automorphic.Sobolev.fourierFun_multiplier (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    fourierFun (SobolevSpace.multiplier hm hC u) =ᵐ[volume] (fun ξ ↦ m ξ • fourierFun u ξ) ∧
      ‖SobolevSpace.multiplier hm hC u‖ ^ 2 =
        ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖m ξ • fourierFun u ξ‖ ^ 2 := by sorry
