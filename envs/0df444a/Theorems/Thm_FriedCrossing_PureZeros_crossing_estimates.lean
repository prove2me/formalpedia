-- Prove2me | Theorems.Thm_FriedCrossing_PureZeros_crossing_estimates
-- name    : FriedCrossing.PureZeros.crossing_estimates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:47:02.962666+00:00
-- url     : https://prove2.me/theorems/1403c169-3749-5fa8-9fa2-65b2c6a9b2fa
-- title:
--   Pure Zeros: crossing estimates
-- statement:
--   THE ESTIMATES. At the crossing σ ∈ (0, 2|s*|/r₀] of a small θ:
--   (i) |e₁(θ,σ)| ≤ K₁|θ|σ (Hadamard from the two axes);
--   (ii) |∂_τe₂(θ,σ)| ≥ r₀|s*|/4 (mean value on [0,σ] from e₂(θ,0) = −s*², e₂(θ,σ) = 0, corrected
--   by the O(|θ|)-bound on ∂²_τe₂ transferred from the axis θ = 0);
--   (iii) hence, if e₁(θ,σ) ≠ 0, the zero's slope |∂_τe₂/e₁| > 2r₀.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L175-L262
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L175-L262

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate

theorem FriedCrossing.PureZeros.crossing_estimates
    (sStar : ℝ → ℝ) (e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) {r₀ K₁ K₂ ε : ℝ}
    (hr₀ : 0 < r₀) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hε : 0 < ε)
    (hd₁ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ)
    (hd₁' : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ)
    (hB₁ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁)
    (hd₂ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ)
    (hd₂' : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ)
    (hd₂'' : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ)
    (hB₂ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂)
    (h₁τ0 : ∀ θ, e₁ θ 0 = 0) (h₁θ0 : ∀ τ, e₁ 0 τ = 0)
    (h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2) (h₂θ0 : ∀ τ, e₂ 0 τ = 0)
    {θ σ : ℝ} (hθε : |θ| < ε) (hθ1 : |θ| < r₀ ^ 2 / (8 * K₂)) (hθ2 : |θ| < r₀ / (16 * K₁))
    (hs : sStar θ < 0) (hσpos : 0 < σ) (hσle : σ ≤ 2 * |sStar θ| / r₀) (hσε : σ < ε)
    (h₂σ : e₂ θ σ = 0) :
    |e₁ θ σ| ≤ K₁ * |θ| * σ ∧ r₀ * |sStar θ| / 4 ≤ |e₂τ θ σ| ∧
      (e₁ θ σ ≠ 0 → 2 * r₀ < |e₂τ θ σ / e₁ θ σ|) := by sorry
