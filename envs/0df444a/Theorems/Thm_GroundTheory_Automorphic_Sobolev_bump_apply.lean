-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_bump_apply
-- name    : GroundTheory.Automorphic.Sobolev.bump_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:43.511331+00:00
-- url     : https://prove2.me/theorems/34d003e1-d649-40c3-8ae3-6c408a625bab
-- title:
--   Sobolev: bump apply
-- statement:
--   The Sobolev construction uses the bump apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L293-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L293-L294

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

theorem GroundTheory.Automorphic.Sobolev.bump_apply (x₀ : E) {r : ℝ} (hr : 0 < r) (x : E) :
    bump x₀ hr x = ((bumpR x₀ hr x : ℝ) : ℂ) := by sorry
