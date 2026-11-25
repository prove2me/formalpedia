-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_tsupport_bump
-- name    : GroundTheory.Automorphic.Sobolev.tsupport_bump
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:47.95459+00:00
-- url     : https://prove2.me/theorems/cdfb91f9-dfa8-4686-bb37-f5534cf3db85
-- title:
--   Sobolev: tsupport bump
-- statement:
--   The Sobolev construction uses the tsupport bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L304-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L304-L309

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.tsupport_bump (x₀ : E) {r : ℝ} (hr : 0 < r) :
    tsupport (bump x₀ hr : E → ℂ) ⊆ Metric.closedBall x₀ (2 * r) := by sorry
