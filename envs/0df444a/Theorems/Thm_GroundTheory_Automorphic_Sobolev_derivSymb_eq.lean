-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_eq
-- name    : GroundTheory.Automorphic.Sobolev.derivSymb_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:48.682364+00:00
-- url     : https://prove2.me/theorems/1e0e9334-4b23-4e06-a9f7-4bc5404e221a
-- title:
--   Sobolev: deriv Symb eq
-- statement:
--   The Sobolev construction uses the deriv Symb eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L346-L348

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
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

theorem GroundTheory.Automorphic.Sobolev.derivSymb_eq {k : ℕ} (w : Fin k → E) (ξ : E) :
    derivSymb w ξ = (2 * Real.pi * Complex.I) ^ k * ∏ j, ((inner ℝ ξ (w j) : ℝ) : ℂ) := by sorry
