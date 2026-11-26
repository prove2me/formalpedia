-- Prove2me | Theorems.Thm_FriedCrossing_Hadamard_continuousAt_Ndiv_entry
-- name    : FriedCrossing.Hadamard.continuousAt_Ndiv_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:39:30.158549+00:00
-- url     : https://prove2.me/theorems/eda9cfde-f16a-5ce9-8f21-e67ddaffeea1
-- title:
--   Hadamard: continuous At Ndiv entry
-- statement:
--   THE HADAMARD STEP. If each entry of M is differentiable in τ with derivative M', M(θ,0) =
--   s*(θ)·1, and each entry of M' is jointly continuous at (0,0), then each entry of N = Ndiv is
--   jointly continuous at (0,0) with value M'(0,0).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L175-L207
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L175-L207

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard

theorem FriedCrossing.Hadamard.continuousAt_Ndiv_entry (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hderiv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ)
    (hM' : ∀ i j, ContinuousAt (fun p : ℝ × ℝ => M' p.1 p.2 i j) (0, 0)) (i j : Fin 2) :
    ContinuousAt (fun p : ℝ × ℝ => Ndiv M M' sStar p.1 p.2 i j) (0, 0) := by sorry
