-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_add_one_of_diffQuot
-- name    : GroundTheory.Automorphic.Sobolev.memSobolev_add_one_of_diffQuot
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:56:36.157474+00:00
-- url     : https://prove2.me/theorems/56e2a956-ef34-41e6-8b9a-87bac7b7d0b1
-- title:
--   Sobolev: mem Sobolev add one of diff Quot
-- statement:
--   The Sobolev construction uses the mem Sobolev add one of diff Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L293-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L293-L355

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

theorem GroundTheory.Automorphic.Sobolev.memSobolev_add_one_of_diffQuot {s : ℝ} (u : SobolevSpace E F s)
    (h : ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) := by sorry
