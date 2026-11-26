-- Prove2me | Theorems.Thm_FriedCrossing_Capstone_fried_fails_at_crossing_of_pure_zero_inputs_ord
-- name    : FriedCrossing.Capstone.fried_fails_at_crossing_of_pure_zero_inputs_ord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:48:31.944799+00:00
-- url     : https://prove2.me/theorems/e838407c-4737-4a1b-85a6-ddea94fa51f5
-- title:
--   Capstone: fried fails at crossing of pure zero inputs ord
-- statement:
--   FRIED FAILS AT THE CROSSING — `hrate_zero` DERIVED. The pure degree-2 zero data enter only as:
--   the symmetric functions e₁, e₂ of the two pure branches with their joint regularity at (0,0)
--   (bounded ∂_θ∂_τe₁; bounded ∂_θ∂²_τe₂) [rank-4 half of input (B)], the boundary values e₁(θ,0) = 0,
--   e₂(θ,0) = −s*² [mirror, A], e₁(0,τ) = e₂(0,τ) = 0 [pinning, D], and at each crossing: e₂ = 0
--   [exactness, E], e₁ ≠ 0 [generic case], and z a continuous root of z² − e₁z + e₂ through 0 [the
--   pure-zero branch]. Everything else is the cluster capstone's ledger. Conclusion adds: the zero's
--   slope at the crossing is ∂_τe₂/e₁ and exceeds 2r₀ in absolute value (steeper than the pole).
--   ⚡9/11 `_ord` form: the exactness quartet (hexact, hacyc, hdual, hdims) is replaced by the one
--   fact it feeds, `zetaOrder c = 0` at each crossing; the original statement is a corollary below.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L437-L555
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_purezeros_9_08.lean#L437-L555

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Capstone
open TorsionCore OrderCount Crossing RateRatio TwinRate PureZeros

theorem FriedCrossing.Capstone.fried_fails_at_crossing_of_pure_zero_inputs_ord
    -- the twin (rate file)
    (sStar : ℝ → ℝ) (a b a' b' : ℝ → ℝ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hderiv_a : ∀ θ τ, HasDerivAt (a θ) (a' θ τ) τ)
    (hderiv_b : ∀ θ τ, HasDerivAt (b θ) (b' θ τ) τ)
    (hcont_a : ContinuousAt (Function.uncurry a) (0, 0))
    (hcont_b : ContinuousAt (Function.uncurry b) (0, 0))
    (hcont_a' : ContinuousAt (Function.uncurry a') (0, 0))
    (hcont_b' : ContinuousAt (Function.uncurry b') (0, 0))
    (ha0 : a 0 0 = r₀) (hb0 : b 0 0 = 0)
    (hsStar0 : sStar 0 = 0) (hsStarc : ContinuousAt sStar 0)
    (hsStarneg : ∀ θ, θ ≠ 0 → sStar θ < 0)
    -- the pure degree-2 pair (this file)
    (e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) {K₁ K₂ ε : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hε : 0 < ε)
    (hd₁ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ)
    (hd₁' : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ)
    (hB₁ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁)
    (hd₂ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ)
    (hd₂' : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ)
    (hd₂'' : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ)
    (hB₂ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂)
    (h₁τ0 : ∀ θ, e₁ θ 0 = 0) (h₁θ0 : ∀ τ, e₁ 0 τ = 0)
    (h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2) (h₂θ0 : ∀ τ, e₂ 0 τ = 0) :
    ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ θ₀ ≤ ε ∧ δ ≤ ε ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (z R : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        τR ≠ 0 →
        (∀ τ, 0 ≤ disc (e₁ θ τ) (e₂ θ τ) → z τ ^ 2 - e₁ θ τ * z τ + e₂ θ τ = 0) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ContinuousAt z τ₀ ∧ z τ₀ = 0 ∧ e₂ θ τ₀ = 0 ∧ e₁ θ τ₀ ≠ 0) →
        (∀ τ₀, twin sStar a b θ τ₀ = 0 → ContinuousAt R τ₀) →
        (∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → R τ * z τ / twin sStar a b θ τ = τR) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 → zetaOrder c = 0) →
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧
          zetaOrder c = 0 ∧
          -- the zero's slope: ∂_τe₂/e₁, steeper than the pole
          HasDerivAt z (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            R σ = τR * ratio ∧ R σ ≠ τR ∧
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by sorry
