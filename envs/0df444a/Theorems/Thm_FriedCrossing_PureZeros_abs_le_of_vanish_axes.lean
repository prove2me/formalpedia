-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_abs_le_of_vanish_axes
-- name    : FriedCrossing.PureZeros.abs_le_of_vanish_axes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:46:52.037463+00:00
-- url     : https://prove2.me/theorems/118740ba-5fba-44bc-9859-b97b5321ba16
-- title:
--   Pure Zeros: abs le of vanish axes
-- statement:
--   f vanishes on both axes and has a bounded mixed partial ⇒ |f(θ,τ)| ≤ K|θ||τ|.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L113-L140
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L113-L140

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.abs_le_of_vanish_axes {f fτ fθτ : ℝ → ℝ → ℝ} {K ε : ℝ} (hε : 0 < ε)
    (h0τ : ∀ θ, f θ 0 = 0) (h0θ : ∀ τ, f 0 τ = 0)
    (hτ : ∀ θ τ, HasDerivAt (f θ) (fτ θ τ) τ)
    (hθ : ∀ θ τ, HasDerivAt (fun θ => fτ θ τ) (fθτ θ τ) θ)
    (hK : ∀ θ τ, |θ| < ε → |τ| < ε → |fθτ θ τ| ≤ K)
    {θ τ : ℝ} (hθε : |θ| < ε) (hτε : |τ| < ε) : |f θ τ| ≤ K * |θ| * |τ| := by sorry
