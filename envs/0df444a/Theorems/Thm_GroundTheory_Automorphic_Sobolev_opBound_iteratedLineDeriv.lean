-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_iteratedLineDeriv
-- name    : GroundTheory.Automorphic.Sobolev.opBound_iteratedLineDeriv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:48.010295+00:00
-- url     : https://prove2.me/theorems/e094a640-9e9e-49de-8811-5956eb9de4b6
-- title:
--   Sobolev: op Bound iterated Line Deriv
-- statement:
--   The Sobolev construction uses the op Bound iterated Line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L456-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L456-L464

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

theorem GroundTheory.Automorphic.Sobolev.opBound_iteratedLineDeriv {k : ℕ} (w : Fin k → E) (s : ℝ) :
    OpBound (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) s (s - k) (∏ j, (2 * Real.pi * ‖w j‖)) := by sorry
