-- Prove2me | Theorems.Thm_FriedCrossing_Derived_pureProdC3_of_C3
-- name    : FriedCrossing.Derived.pureProdC3_of_C3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:29.530043+00:00
-- url     : https://prove2.me/theorems/36fda73d-8a2f-5e5d-a66e-76b7f84ca658
-- title:
--   Derived: pure Prod C3 of C3
-- statement:
--   ClusterC3 ⇒ PureProdC3 on the unit square.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L539-L554
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L539-L554

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

theorem FriedCrossing.Derived.pureProdC3_of_C3 (h : ClusterC3 M A) :
    ∃ K₂ : ℝ, PureProdC3 (E₂f M A) (pτ (E₂f M A)) (pτ (pτ (E₂f M A)))
      (pθ (pτ (pτ (E₂f M A)))) K₂ 1 := by sorry
