-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_sm_of_weak_deriv_closed
-- name    : GlobalTheory.RealWeil.sm_of_weak_deriv_closed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:16:50.262489+00:00
-- url     : https://prove2.me/theorems/b7b90f33-5c75-40e4-a834-58c12baab6db
-- title:
--   Real Weil: sm of weak deriv closed
-- statement:
--   The Real Weil construction uses the sm of weak deriv closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergSmoothOfWeakDerivativeClosedSet.lean#L32-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergSmoothOfWeakDerivativeClosedSet.lean#L32-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
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
open GlobalTheory GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.sm_of_weak_deriv_closed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ)
    (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) →
    (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) →
    (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B,
    (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) →
    (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) →
    ∀ f ∈ Θ, Sm ρ f := by sorry
