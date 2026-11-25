-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_comm_prinOp
-- name    : GroundTheory.Automorphic.Sobolev.hasOrder_comm_prinOp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:47.931859+00:00
-- url     : https://prove2.me/theorems/c86ba74b-67cd-4a70-8506-2602078a90a9
-- title:
--   Sobolev: has Order comm prin Op
-- statement:
--   The Sobolev construction uses the has Order comm prin Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L399-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L399-L403

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
variable {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E)

theorem GroundTheory.Automorphic.Sobolev.hasOrder_comm_prinOp (ψ : 𝓢(E, ℂ)) : HasOrder (comm (prinOp a w) ψ) ((m : ℝ) - 1) := by sorry
