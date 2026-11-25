-- Prove2me | Theorems.Thm_GlobalTheory_T_commuting_algebras_finite_span
-- name    : GlobalTheory.T.commuting_algebras_finite_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:44.462708+00:00
-- url     : https://prove2.me/theorems/da7c56dc-da4f-4608-a874-cf6019e2569f
-- title:
--   T: commuting algebras finite span
-- statement:
--   The T construction uses the commuting algebras finite span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommutingAlgebrasFiniteSpanStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommutingAlgebrasFiniteSpanStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutingAlgebrasFiniteSpan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutingAlgebrasFiniteSpanStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.commuting_algebras_finite_span : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M)), (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ m : M, (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) → ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by sorry
