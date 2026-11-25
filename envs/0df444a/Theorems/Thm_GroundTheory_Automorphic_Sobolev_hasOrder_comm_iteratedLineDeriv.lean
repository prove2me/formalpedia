-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_comm_iteratedLineDeriv
-- name    : GroundTheory.Automorphic.Sobolev.hasOrder_comm_iteratedLineDeriv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:35.901482+00:00
-- url     : https://prove2.me/theorems/e4a7c58a-cc12-5cd6-8cc9-608d5d666964
-- title:
--   Sobolev: has Order comm iterated Line Deriv
-- statement:
--   The Sobolev construction uses the has Order comm iterated Line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L269-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L269-L284

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

theorem GroundTheory.Automorphic.Sobolev.hasOrder_comm_iteratedLineDeriv {k : ℕ} (w : Fin k → E) (ψ : 𝓢(E, ℂ)) :
    HasOrder (comm (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) ψ) (k - 1) := by sorry
