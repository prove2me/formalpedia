-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_lineDeriv_le
-- name    : GroundTheory.Automorphic.Sobolev.sob_lineDeriv_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:24.450672+00:00
-- url     : https://prove2.me/theorems/7c5b6b90-09a2-5e69-9efc-c28d29d43199
-- title:
--   Sobolev: sob line Deriv le
-- statement:
--   The Sobolev construction uses the sob line Deriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L609-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L609-L614

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

theorem GroundTheory.Automorphic.Sobolev.sob_lineDeriv_le (v : E) {s : ℝ} {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    sob (s - 1) (LineDeriv.lineDerivOp v u) ≤ ENNReal.ofReal (2 * Real.pi * ‖v‖) * sob s u := by sorry
