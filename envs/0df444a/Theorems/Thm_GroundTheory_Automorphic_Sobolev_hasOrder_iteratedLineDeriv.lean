-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_iteratedLineDeriv
-- name    : GroundTheory.Automorphic.Sobolev.hasOrder_iteratedLineDeriv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:00:01.702924+00:00
-- url     : https://prove2.me/theorems/2a21bf00-53c9-4714-b8f5-5db427e7a82c
-- title:
--   Sobolev: has Order iterated Line Deriv
-- statement:
--   The Sobolev construction uses the has Order iterated Line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L99-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L99-L112

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

theorem GroundTheory.Automorphic.Sobolev.hasOrder_iteratedLineDeriv {k : ℕ} (w : Fin k → E) :
    HasOrder (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) k := by sorry
