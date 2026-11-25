-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_bump_le
-- name    : GroundTheory.Automorphic.Sobolev.norm_bump_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:27.804667+00:00
-- url     : https://prove2.me/theorems/37116ff2-6061-436f-844e-c898532d901c
-- title:
--   Sobolev: norm bump le
-- statement:
--   The Sobolev construction uses the norm bump le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L300-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L300-L302

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

theorem GroundTheory.Automorphic.Sobolev.norm_bump_le (x₀ : E) {r : ℝ} (hr : 0 < r) (x : E) : ‖bump x₀ hr x‖ ≤ 1 := by sorry
