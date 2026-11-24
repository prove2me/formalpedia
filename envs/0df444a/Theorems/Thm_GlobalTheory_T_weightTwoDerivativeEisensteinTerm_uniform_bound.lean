-- Prove2me | Theorems.Thm_GlobalTheory_T_weightTwoDerivativeEisensteinTerm_uniform_bound
-- name    : GlobalTheory.T.weightTwoDerivativeEisensteinTerm_uniform_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:55.286689+00:00
-- url     : https://prove2.me/theorems/534ee1b9-c5a4-41c7-ba3f-c487f6fcfb7e
-- title:
--   T: weight Two Derivative Eisenstein Term uniform bound
-- statement:
--   The T construction uses the weight Two Derivative Eisenstein Term uniform bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightTwoDerivativeEisensteinTermUniformBoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightTwoDerivativeEisensteinTermUniformBoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightTwoDerivativeEisensteinTermUniformBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightTwoDerivativeEisensteinTermUniformBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weightTwoDerivativeEisensteinTerm_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by sorry
