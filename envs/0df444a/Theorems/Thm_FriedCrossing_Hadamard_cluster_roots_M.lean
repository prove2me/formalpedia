-- Prove2me | Theorems.Thm_FriedCrossing_Hadamard_cluster_roots_M
-- name    : FriedCrossing.Hadamard.cluster_roots_M
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:57:27.80062+00:00
-- url     : https://prove2.me/theorems/5a06c849-25ca-5d97-a882-ee5fd4957f1d
-- title:
--   Hadamard: cluster roots M
-- statement:
--   CLUSTER ROOTS FOR THE ACTUAL MATRIX: z is a root of the characteristic polynomial of
--   M(θ,τ) iff z = s*(θ) + τ·w±(tr N, det N). Consumes only M(θ,0) = s*·1 and disc ≥ 0.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L242-L249
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L242-L249

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard

theorem FriedCrossing.Hadamard.cluster_roots_M (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ)
    (hD : 0 ≤ TwinRate.disc (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det) (z : ℝ) :
    z ^ 2 - (M θ τ).trace * z + (M θ τ).det = 0 ↔
      z = sStar θ + τ * TwinRate.wPlus (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det ∨
      z = sStar θ + τ * TwinRate.wMinus (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det := by sorry
