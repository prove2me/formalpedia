-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_rpow_eq_sqrt_pow
-- name    : GroundTheory.Automorphic.Sobolev.rpow_eq_sqrt_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:20:02.056772+00:00
-- url     : https://prove2.me/theorems/a8fa3529-ec03-4091-bada-ede5b2353215
-- title:
--   Sobolev: rpow eq sqrt pow
-- statement:
--   The Sobolev construction uses the rpow eq sqrt pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L22-L26

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

theorem GroundTheory.Automorphic.Sobolev.rpow_eq_sqrt_pow (ξ : E) (k : ℕ) :
    (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) = Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k := by sorry
