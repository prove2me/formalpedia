-- Prove2me | Theorems.Thm_GlobalTheory_T_weyl_number_operator_commutation_alt
-- name    : GlobalTheory.T.weyl_number_operator_commutation_alt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:38.063806+00:00
-- url     : https://prove2.me/theorems/2fc22e10-e930-5deb-919a-6cb464756911
-- title:
--   T: weyl number operator commutation alt
-- statement:
--   The T construction uses the weyl number operator commutation alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeylNumberOperatorCommutationStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeylNumberOperatorCommutationStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeylNumberOperatorCommutation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeylNumberOperatorCommutationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weyl_number_operator_commutation_alt : ∀ (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A] [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A), (∀ x, J (J x) = -x) → (∀ u v, D (u + v) = D u + D v) → (∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v) → (∀ u v, D u * D v - D v * D u = (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1) → (∀ z, c z = D z - Complex.I • D (J z)) → (∀ z, a z = -(D z + Complex.I • D (J z))) → N = ∑ j, c (e j) * a (e j) → (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧ (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by sorry
