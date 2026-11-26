-- Prove2me | Theorems.Thm_FriedCrossing_Derived_hasDerivAt_Ndiv_entry
-- name    : FriedCrossing.Derived.hasDerivAt_Ndiv_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:27.573208+00:00
-- url     : https://prove2.me/theorems/8e491a2c-3335-56c2-b2a1-3d30ab553db0
-- title:
--   Derived: has Deriv At Ndiv entry
-- statement:
--   The Derived construction uses the has Deriv At Ndiv entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L463-L472
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L463-L472

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

theorem FriedCrossing.Derived.hasDerivAt_Ndiv_entry (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun τ => Ndiv M (Mτ M) sStar θ τ i j) (Nτ M θ τ i j) τ := by sorry
