-- Prove2me | Theorems.Thm_GlobalTheory_T_weightNear_diagonalOperators_bounds
-- name    : GlobalTheory.T.weightNear_diagonalOperators_bounds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:09.415188+00:00
-- url     : https://prove2.me/theorems/d221b862-9ede-5c41-a3f4-90e42e80f6cd
-- title:
--   T: weight Near diagonal Operators bounds
-- statement:
--   The T construction uses the weight Near diagonal Operators bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WeightNearDiagonalOperatorsBoundsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WeightNearDiagonalOperatorsBoundsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBounds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weightNear_diagonalOperators_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by sorry
