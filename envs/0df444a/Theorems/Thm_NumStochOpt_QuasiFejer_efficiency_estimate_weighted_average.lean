-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_efficiency_estimate_weighted_average
-- name    : NumStochOpt.QuasiFejer.efficiency_estimate_weighted_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T20:43:38.73186+00:00
-- url     : https://prove2.me/theorems/08856594-b5df-41f3-a93e-bedb73dfa09b
-- title:
--   p. 147 — efficiency estimate E F⁰(x̄^s) − F⁰(x*) ≤ (2Σρ_k)⁻¹[E‖x*−x⁰‖² + Σ E(2ρ_k|γ₀(k)| + ρ_k²‖ξ⁰(k)‖²)]
-- statement:
--   Let $X\subseteq\mathbb R^n$ be a nonempty convex compact set and $F$ convex and continuous on $X$, with optimal set $X^*$ and a point $x^*\in X^*$. On a probability space let $x^0,x^1,\dots$ be measurable random vectors with $x^0\in X$, $\xi^0(k)$ integrable random directions, $\gamma_0(k)$ random variables measurable with respect to $\sigma(x^0,\dots,x^k)$, and $\rho_0,\rho_1,\dots\ge0$ **deterministic** step sizes. Assume (6.11), $x^{k+1}=\pi_X[x^k-\rho_k\xi^0(k)]$, and (6.12) at $x^*$ for every $k$, and that $\rho_k|\gamma_0(k)|$ and $\rho_k^2\|\xi^0(k)\|^2$ are integrable. Fix $s$ with $\sum_{k=0}^s\rho_k>0$ and let $\bar x^s=(\sum_{k=0}^s\rho_kx^k)(\sum_{k=0}^s\rho_k)^{-1}$. Then
--   $$
--   E F(\bar x^s)-F(x^*)\le\Big(2\sum_{k=0}^s\rho_k\Big)^{-1}\Big[E\|x^*-x^0\|^2+\sum_{k=0}^sE\big(2\rho_k|\gamma_0(k)|+\rho_k^2\|\xi^0(k)\|^2\big)\Big].
--   $$
--
--   This is a non-asymptotic accuracy bound for the averaged iterate of the stochastic quasigradient projection method; with $\rho_k$ of order $k^{-1/2}$ and bounded second moments it gives the familiar $O(\log s/\sqrt s)$ rate.
--
--   **Formalization Note** The book writes an unspecified constant $C$ in front of the last sum; its own derivation (pp. 145–147) gives the constant $2$ on the $\rho_k|\gamma_0(k)|$ term and $1$ on the $\rho_k^2\|\xi^0(k)\|^2$ term, which are stated here. The book's hypothesis "the $\rho_k$ are independent of $(x^0,\dots,x^k)$" is read as deterministic step sizes. The page omits the expectation in front of the last sum; since the left side is an expectation it is restored. Only (6.12) at the single point $x^*$ is used.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 147, final display of §6.2.1 (weighted average x̄^s defined on p. 146)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **Efficiency estimate for the weighted average** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988),
p. 147, final display of §6.2.1). For the projection method (6.11) with deterministic step sizes
`ρ_k ≥ 0` (the book's "ρ_k independent of (x⁰, …, x^k)") and directions satisfying (6.12) at an
optimal point `x*`, the weighted average `x̄^s = (∑_{k≤s} ρ_k x^k)/(∑_{k≤s} ρ_k)` satisfies
`E F(x̄^s) - F(x*) ≤ (2∑_{k≤s} ρ_k)⁻¹ [E‖x* - x⁰‖² + ∑_{k≤s} E(2ρ_k|γ₀(k)| + ρ_k²‖ξ⁰(k)‖²)]`.
The book writes an unspecified constant `C` in front of the last sum; its proof gives the
constant `2` on the `ρ_k|γ₀(k)|` term and `1` on the `ρ_k²‖ξ⁰(k)‖²` term. -/
theorem efficiency_estimate_weighted_average {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (γ₀ : ℕ → Ω → ℝ) (s : ℕ)
    (hFconv : ConvexOn ℝ X F) (hFcont : ContinuousOn F X)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hx_meas : ∀ k, Measurable (x k)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ_int : ∀ k, Integrable (ξ k) μ)
    (hγ_adapt : ∀ k, StronglyMeasurable[historySigma x k] (γ₀ k))
    (hrec : ∀ k ω, x (k + 1) ω = projX X (x k ω - ρ k • ξ k ω))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ optimalSet F X)
    (hqg : ∀ k, ∀ᵐ ω ∂μ,
      F xstar - F (x k ω) ≥ ⟪(condExp (historySigma x k) μ (ξ k)) ω, xstar - x k ω⟫_ℝ + γ₀ k ω)
    (hρ_nonneg : ∀ k, 0 ≤ ρ k) (hρ_pos : 0 < ∑ k ∈ Finset.range (s + 1), ρ k)
    (hγ_int : ∀ k, Integrable (fun ω => ρ k * |γ₀ k ω|) μ)
    (hξ_sq : ∀ k, Integrable (fun ω => ρ k ^ 2 * ‖ξ k ω‖ ^ 2) μ) :
    (∫ ω, F (weightedAvg ρ x s ω) ∂μ) - F xstar ≤
      (2 * ∑ k ∈ Finset.range (s + 1), ρ k)⁻¹ *
        ((∫ ω, ‖xstar - x 0 ω‖ ^ 2 ∂μ) +
          ∑ k ∈ Finset.range (s + 1),
            ∫ ω, (2 * ρ k * |γ₀ k ω| + ρ k ^ 2 * ‖ξ k ω‖ ^ 2) ∂μ) := by sorry

end NumStochOpt.QuasiFejer
