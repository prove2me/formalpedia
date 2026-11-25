-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_le_of_mul_sqrt_pow_le
-- name    : GroundTheory.Automorphic.Sobolev.norm_le_of_mul_sqrt_pow_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:39.371354+00:00
-- url     : https://prove2.me/theorems/467f1556-d9a8-486a-810e-87602c4e1f8e
-- title:
--   Sobolev: norm le of mul sqrt pow le
-- statement:
--   The Sobolev construction uses the norm le of mul sqrt pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L28-L35

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

theorem GroundTheory.Automorphic.Sobolev.norm_le_of_mul_sqrt_pow_le {f : E → ℂ} {C : ℝ} {k : ℕ}
    (h : ∀ ξ, ‖f ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k ≤ C) (ξ : E) :
    ‖f ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) := by sorry
