-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_abs_weight_sub_le
-- name    : GroundTheory.Automorphic.Sobolev.abs_weight_sub_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:57.636227+00:00
-- url     : https://prove2.me/theorems/54baf599-5cd9-5bef-91c2-e813db928671
-- title:
--   Sobolev: abs weight sub le
-- statement:
--   The Sobolev construction uses the abs weight sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L159-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L159-L188

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.abs_weight_sub_le (r : ℝ) (ξ η : E) :
    |(1 + ‖ξ‖ ^ 2) ^ (r / 2) - (1 + ‖η‖ ^ 2) ^ (r / 2)| ≤
      |r| * 2 ^ (|r - 1| / 2) * ‖ξ - η‖ * (1 + ‖ξ - η‖ ^ 2) ^ (|r - 1| / 2) *
        (1 + ‖η‖ ^ 2) ^ ((r - 1) / 2) := by sorry
