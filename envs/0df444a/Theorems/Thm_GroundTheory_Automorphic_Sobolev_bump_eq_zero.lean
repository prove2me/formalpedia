-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_bump_eq_zero
-- name    : GroundTheory.Automorphic.Sobolev.bump_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:22.022441+00:00
-- url     : https://prove2.me/theorems/df0a13aa-e5d7-5ee1-959d-02601af533c8
-- title:
--   Sobolev: bump eq zero
-- statement:
--   The Sobolev construction uses the bump eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L311-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L311-L313

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

theorem GroundTheory.Automorphic.Sobolev.bump_eq_zero (x₀ : E) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∉ Metric.closedBall x₀ (2 * r)) :
    bump x₀ hr x = 0 := by sorry
