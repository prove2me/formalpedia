-- Prove2me | Theorems.Thm_FriedCrossing_Derived_traceDetC1_of_C3
-- name    : FriedCrossing.Derived.traceDetC1_of_C3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:28.360828+00:00
-- url     : https://prove2.me/theorems/6b24041e-f5ed-5226-b8d7-fa112f499bc7
-- title:
--   Derived: trace Det C1 of C3
-- statement:
--   ClusterC3 (+ semisimplicity at τ = 0) ⇒ TraceDetC1 with the explicit derivatives.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L511-L517
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L511-L517

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}

theorem FriedCrossing.Derived.traceDetC1_of_C3 (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    TraceDetC1 M (Mτ M) sStar (aτ M) (bτ M sStar) := by sorry
