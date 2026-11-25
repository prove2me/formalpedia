-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isLocal_iteratedLineDeriv
-- name    : GroundTheory.Automorphic.Sobolev.isLocal_iteratedLineDeriv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:31.797304+00:00
-- url     : https://prove2.me/theorems/b1623320-6c36-4e57-949f-8c9eef433ae4
-- title:
--   Sobolev: is Local iterated Line Deriv
-- statement:
--   The Sobolev construction uses the is Local iterated Line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L172-L174

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

theorem GroundTheory.Automorphic.Sobolev.isLocal_iteratedLineDeriv {k : ℕ} (w : Fin k → E) :
    IsLocal (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) := by sorry
