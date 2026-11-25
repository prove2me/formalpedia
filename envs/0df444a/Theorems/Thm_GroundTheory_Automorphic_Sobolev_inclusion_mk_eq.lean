-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_inclusion_mk_eq
-- name    : GroundTheory.Automorphic.Sobolev.inclusion_mk_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:49.57541+00:00
-- url     : https://prove2.me/theorems/0c07ae25-2533-4dbc-8c87-08ce8bc9f812
-- title:
--   Sobolev: inclusion mk eq
-- statement:
--   The Sobolev construction uses the inclusion mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L357-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L357-L361

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

theorem GroundTheory.Automorphic.Sobolev.inclusion_mk_eq {s : ℝ} (u : SobolevSpace E F s)
    (hu : MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u)) :
    SobolevSpace.inclusion (le_add_of_nonneg_right zero_le_one) (SobolevSpace.mk (s := s + 1) _ hu) = u := by sorry
