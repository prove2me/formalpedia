-- Prove2me | Theorems.Thm_FriedCrossing_Hadamard_entry_slope_eq
-- name    : FriedCrossing.Hadamard.entry_slope_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:39:49.072881+00:00
-- url     : https://prove2.me/theorems/e4d03a42-0cb8-4bdc-94f0-cafa5788eb41
-- title:
--   Hadamard: entry slope eq
-- statement:
--   Entrywise mean value theorem: for τ ≠ 0 the difference quotient of an entry equals the
--   τ-derivative of that entry at some ξ strictly between 0 and τ.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L157-L170
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L157-L170

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard

theorem FriedCrossing.Hadamard.entry_slope_eq {f f' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : ∃ ξ, |ξ| < |τ| ∧ (f τ - f 0) / τ = f' ξ := by sorry
