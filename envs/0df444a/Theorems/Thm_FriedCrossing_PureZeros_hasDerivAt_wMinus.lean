-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_hasDerivAt_wMinus
-- name    : FriedCrossing.PureZeros.hasDerivAt_wMinus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:47:11.317796+00:00
-- url     : https://prove2.me/theorems/800446b2-a470-5fe8-9ee7-58edceb9d337
-- title:
--   Pure Zeros: has Deriv At w Minus
-- statement:
--   The Pure Zeros construction uses the has Deriv At w Minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L270-L277
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L270-L277

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.hasDerivAt_wMinus {A B : ℝ → ℝ} {a' b' τ : ℝ} (hA : HasDerivAt A a' τ)
    (hB : HasDerivAt B b' τ) (hD : 0 < disc (A τ) (B τ)) :
    HasDerivAt (fun t => wMinus (A t) (B t)) (dwMinus (A τ) (B τ) a' b') τ := by sorry
