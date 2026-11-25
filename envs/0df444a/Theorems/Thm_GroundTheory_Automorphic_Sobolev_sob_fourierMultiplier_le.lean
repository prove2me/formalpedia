-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_fourierMultiplier_le
-- name    : GroundTheory.Automorphic.Sobolev.sob_fourierMultiplier_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:49:26.865837+00:00
-- url     : https://prove2.me/theorems/07c7d4f4-6bd2-5669-b2a4-9d9cee563a26
-- title:
--   Sobolev: sob fourier Multiplier le
-- statement:
--   The Sobolev construction uses the sob fourier Multiplier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L597-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L597-L603

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

theorem GroundTheory.Automorphic.Sobolev.sob_fourierMultiplier_le {m : E → ℂ} (hm : m.HasTemperateGrowth) {C s t : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    sob t (fourierMultiplierCLM ℂ m u) ≤ ENNReal.ofReal C * sob s u := by sorry
