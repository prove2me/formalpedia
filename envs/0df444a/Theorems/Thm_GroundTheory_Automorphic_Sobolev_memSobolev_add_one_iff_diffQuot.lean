-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_add_one_iff_diffQuot
-- name    : GroundTheory.Automorphic.Sobolev.memSobolev_add_one_iff_diffQuot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:12.048895+00:00
-- url     : https://prove2.me/theorems/71168004-6107-427d-8162-990c67067222
-- title:
--   Sobolev: mem Sobolev add one iff diff Quot
-- statement:
--   The Sobolev construction uses the mem Sobolev add one iff diff Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L365-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L365-L371

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
open Filter Topology

theorem GroundTheory.Automorphic.Sobolev.memSobolev_add_one_iff_diffQuot {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C := by sorry
