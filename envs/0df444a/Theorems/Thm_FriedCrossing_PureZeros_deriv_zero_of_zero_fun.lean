-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_deriv_zero_of_zero_fun
-- name    : FriedCrossing.PureZeros.deriv_zero_of_zero_fun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:46:59.518204+00:00
-- url     : https://prove2.me/theorems/2fce927e-a21b-5afa-9fab-295091e186be
-- title:
--   Pure Zeros: deriv zero of zero fun
-- statement:
--   Derivatives of a function vanishing identically on a line vanish there too.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L161-L166
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L161-L166

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.deriv_zero_of_zero_fun {g gτ : ℝ → ℝ} (h0 : ∀ τ, g τ = 0)
    (hd : ∀ τ, HasDerivAt g (gτ τ) τ) (τ : ℝ) : gτ τ = 0 := by sorry
