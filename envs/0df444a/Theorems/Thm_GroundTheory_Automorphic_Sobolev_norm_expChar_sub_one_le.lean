-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_expChar_sub_one_le
-- name    : GroundTheory.Automorphic.Sobolev.norm_expChar_sub_one_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:49.184854+00:00
-- url     : https://prove2.me/theorems/b3435860-a7cd-44a3-ae73-4ab5087af958
-- title:
--   Sobolev: norm exp Char sub one le
-- statement:
--   The Sobolev construction uses the norm exp Char sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L201-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L201-L205

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

theorem GroundTheory.Automorphic.Sobolev.norm_expChar_sub_one_le (a ξ : E) :
    ‖expChar a ξ - 1‖ ≤ 2 * Real.pi * |inner ℝ ξ a| := by sorry
