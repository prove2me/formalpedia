-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_hasDerivAt_zero_branch
-- name    : FriedCrossing.PureZeros.hasDerivAt_zero_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:47:52.057405+00:00
-- url     : https://prove2.me/theorems/18b42620-0747-5b99-8c73-c74d33db6912
-- title:
--   Pure Zeros: has Deriv At zero branch
-- statement:
--   THE PURE-ZERO BRANCH. A continuous root z of Q(τ; ·) = z² − e₁(τ)z + e₂(τ) with z(σ) = 0,
--   where e₂(σ) = 0 and e₁(σ) ≠ 0, coincides near σ with the explicit root vanishing at σ and is
--   differentiable there with slope ∂_τe₂(σ)/e₁(σ).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L319-L380
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L319-L380

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.hasDerivAt_zero_branch {e₁ e₂ z : ℝ → ℝ} {e₁' e₂' σ : ℝ}
    (hd₁ : HasDerivAt e₁ e₁' σ) (hd₂ : HasDerivAt e₂ e₂' σ)
    (h₂σ : e₂ σ = 0) (h₁σ : e₁ σ ≠ 0)
    (hzQ : ∀ τ, 0 ≤ disc (e₁ τ) (e₂ τ) → z τ ^ 2 - e₁ τ * z τ + e₂ τ = 0)
    (hzc : ContinuousAt z σ) (hz0 : z σ = 0) :
    HasDerivAt z (e₂' / e₁ σ) σ := by sorry
