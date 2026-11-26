-- Prove2me | Theorems.Thm_FriedCrossing_Hadamard_continuousAt_det_Ndiv
-- name    : FriedCrossing.Hadamard.continuousAt_det_Ndiv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:46:23.932138+00:00
-- url     : https://prove2.me/theorems/a9ed63bd-acaa-5e5b-8c45-050c465ff643
-- title:
--   Hadamard: continuous At det Ndiv
-- statement:
--   The Hadamard construction uses the continuous At det Ndiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L219-L226
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L219-L226

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard

theorem FriedCrossing.Hadamard.continuousAt_det_Ndiv (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hderiv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ)
    (hM' : ∀ i j, ContinuousAt (fun p : ℝ × ℝ => M' p.1 p.2 i j) (0, 0)) :
    ContinuousAt (fun p : ℝ × ℝ => (Ndiv M M' sStar p.1 p.2).det) (0, 0) := by sorry
