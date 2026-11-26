-- Prove2me | Theorems.Thm_FriedCrossing_Derived_hasDerivAt_det_Ndiv
-- name    : FriedCrossing.Derived.hasDerivAt_det_Ndiv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:50:06.040805+00:00
-- url     : https://prove2.me/theorems/6b1194d3-925a-5b92-a222-723fdc1c00b1
-- title:
--   Derived: has Deriv At det Ndiv
-- statement:
--   The Derived construction uses the has Deriv At det Ndiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L480-L485
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L480-L485

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

theorem FriedCrossing.Derived.hasDerivAt_det_Ndiv (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) :
    HasDerivAt (fun τ => (Ndiv M (Mτ M) sStar θ τ).det) (bτ M sStar θ τ) τ := by sorry
