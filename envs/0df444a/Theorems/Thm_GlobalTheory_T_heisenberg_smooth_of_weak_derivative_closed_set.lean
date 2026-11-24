-- Prove2me | Theorems.Thm_GlobalTheory_T_heisenberg_smooth_of_weak_derivative_closed_set
-- name    : GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:24.262861+00:00
-- url     : https://prove2.me/theorems/a76bf487-bddf-48d6-ad8b-30f886279df8
-- title:
--   T: heisenberg smooth of weak derivative closed set
-- statement:
--   The T construction uses the heisenberg smooth of weak derivative closed set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergSmoothOfWeakDerivativeClosedSetStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergSmoothOfWeakDerivativeClosedSetStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSetStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) → (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) → (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B, (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) → (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) → ∀ f ∈ Θ, Sm ρ f := by sorry
