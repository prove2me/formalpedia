-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_add_one_iff_lineDeriv
-- name    : GroundTheory.Automorphic.Sobolev.memSobolev_add_one_iff_lineDeriv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:54.0628+00:00
-- url     : https://prove2.me/theorems/dc6fdb3a-4e79-40e4-ba9d-b039ec012afd
-- title:
--   Sobolev: mem Sobolev add one iff line Deriv
-- statement:
--   The Sobolev construction uses the mem Sobolev add one iff line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L155-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L155-L193

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
open LineDeriv

theorem GroundTheory.Automorphic.Sobolev.memSobolev_add_one_iff_lineDeriv {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, MemSobolev s 2 (∂_{v} (SobolevSpace.toDistribution u)) := by sorry
