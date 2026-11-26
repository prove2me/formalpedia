-- Prove2me | Theorems.Thm_FriedCrossing_RateRatio_linearArrival_of_one_add_o
-- name    : FriedCrossing.RateRatio.linearArrival_of_one_add_o
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:54:50.859076+00:00
-- url     : https://prove2.me/theorems/e0baa709-d5f4-4127-bcfd-b70f3c9036c0
-- title:
--   Rate Ratio: linear Arrival of one add o
-- statement:
--   The memos' `(1 + o(1))` form implies linear arrival.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L188-L198
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L188-L198

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio

theorem FriedCrossing.RateRatio.linearArrival_of_one_add_o {f e : ℝ → ℝ} {c σ : ℝ}
    (hf : ∀ τ, f τ = c * (τ - σ) * (1 + e τ)) (he : Tendsto e (𝓝[≠] σ) (𝓝 0)) :
    LinearArrival f c σ := by sorry
