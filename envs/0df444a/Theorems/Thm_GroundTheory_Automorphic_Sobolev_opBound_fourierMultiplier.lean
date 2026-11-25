-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_fourierMultiplier
-- name    : GroundTheory.Automorphic.Sobolev.opBound_fourierMultiplier
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:58.219251+00:00
-- url     : https://prove2.me/theorems/d478389e-228a-4f4b-b5c5-caedd98dff70
-- title:
--   Sobolev: op Bound fourier Multiplier
-- statement:
--   The Sobolev construction uses the op Bound fourier Multiplier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L452-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L452-L454

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

theorem GroundTheory.Automorphic.Sobolev.opBound_fourierMultiplier {g : E → ℂ} (hg : g.HasTemperateGrowth) {C s t : ℝ}
    (hC : ∀ ξ, ‖g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) : OpBound (fourierMultiplierCLM ℂ g) s t C := by sorry
