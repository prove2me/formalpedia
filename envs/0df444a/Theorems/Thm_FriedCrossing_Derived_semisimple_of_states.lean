-- Prove2me | Theorems.Thm_FriedCrossing_Derived_semisimple_of_states
-- name    : FriedCrossing.Derived.semisimple_of_states
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:32.156656+00:00
-- url     : https://prove2.me/theorems/7e01c664-87eb-5875-914b-fd48a796d694
-- title:
--   Derived: semisimple of states
-- statement:
--   The ledger shape: for every θ, two independent states at s*(θ) in the degree-1 cluster at g_hyp
--   ⇒ M(θ,0) = s*(θ)·1.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L720-L725
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L720-L725

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived

theorem FriedCrossing.Derived.semisimple_of_states (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (hstates : ∀ θ, ∃ v₁ v₂ : Fin 2 → ℝ, LinearIndependent ℝ ![v₁, v₂] ∧
      M θ 0 *ᵥ v₁ = sStar θ • v₁ ∧ M θ 0 *ᵥ v₂ = sStar θ • v₂) :
    ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by sorry
