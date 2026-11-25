-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_mem
-- name    : GroundTheory.Automorphic.Sobolev.sob_of_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:51:22.926987+00:00
-- url     : https://prove2.me/theorems/73ad328c-6a4a-4e0f-b5e4-844cf7405138
-- title:
--   Sobolev: sob of mem
-- statement:
--   The Sobolev construction uses the sob of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L367-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L367-L368

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
variable (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.sob_of_mem {s : ℝ} {u : 𝓢'(E, ℂ)} (h : MemSobolev s 2 u) :
    sob s u = ‖(SobolevSpace.mk u h : SobolevSpace E ℂ s)‖ₑ := by sorry
