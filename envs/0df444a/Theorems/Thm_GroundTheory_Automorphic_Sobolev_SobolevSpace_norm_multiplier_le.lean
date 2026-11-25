-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_multiplier_le
-- name    : GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_multiplier_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:08.412903+00:00
-- url     : https://prove2.me/theorems/97cb2caf-ff6a-4c8d-a31b-05fc843b39cf
-- title:
--   Sobolev Space: norm multiplier le
-- statement:
--   The Sobolev Space construction uses the norm multiplier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L323-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L323-L326

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
open GroundTheory.Automorphic.Sobolev.SobolevSpace

theorem GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_multiplier_le (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) :
    ‖multiplier (E := E) (F := F) hm hC‖ ≤ C := by sorry
