-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_mulPrin_le
-- name    : GroundTheory.Automorphic.Sobolev.sob_mulPrin_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:14.283505+00:00
-- url     : https://prove2.me/theorems/629a834f-997e-4973-bffa-acf0deca3b97
-- title:
--   Sobolev: sob mul Prin le
-- statement:
--   The Sobolev construction uses the sob mul Prin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L553-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L553-L585

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

theorem GroundTheory.Automorphic.Sobolev.sob_mulPrin_le (χ : 𝓢(E, ℂ)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖χ x‖ ≤ M) (r : ℝ)
    {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    sob r (mulPrin χ r u) ≤ ENNReal.ofReal M * sob r u := by sorry
