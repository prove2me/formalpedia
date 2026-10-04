-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_theorem_6_2_projection_method_converges
-- name    : NumStochOpt.QuasiFejer.theorem_6_2_projection_method_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T20:46:04.01959+00:00
-- url     : https://prove2.me/theorems/72b847fe-14ae-4cb1-959e-dc68db9a46f1
-- title:
--   Theorem 6.2 — the stochastic quasigradient projection method converges a.s. to a point of X*
-- statement:
--   Consider minimizing $F:\mathbb R^n\to\mathbb R$ over $X\subseteq\mathbb R^n$, with optimal set $X^*$. On a probability space let $x^0,x^1,\dots$ be measurable random vectors with $x^0\in X$, let $\xi^0(s)$ be integrable random directions, and let $\rho_s$ (step sizes) and $\gamma_0(s)$ be random variables that depend only on the history, i.e. are measurable with respect to $\sigma(x^0,\dots,x^s)$. The method is
--   $$
--   x^{s+1}=\pi_X\big[x^s-\rho_s\xi^0(s)\big],\qquad s=0,1,\dots\qquad(6.11)
--   $$
--   with directions satisfying, for every $x^*\in X^*$ and every $s$, almost surely
--   $$
--   F(x^*)-F(x^s)\ge\big\langle E\{\xi^0(s)\mid x^0,\dots,x^s\},x^*-x^s\big\rangle+\gamma_0(s).\qquad(6.12)
--   $$
--   Assume
--
--   1. $F$ is convex and continuous on $X$;
--   2. $X$ is a nonempty convex compact set;
--   3. with probability 1, $\rho_s\ge0$ for all $s$ and $\sum_{s=0}^\infty\rho_s=\infty$, and
--   $$
--   \sum_{s=0}^\infty E\{\rho_s|\gamma_0(s)|+\rho_s^2\|\xi^0(s)\|^2\}<\infty.\qquad(6.15)
--   $$
--
--   Then with probability 1 the sequence $x^s$ converges and $\lim_s x^s\in X^*$.
--
--   This is the basic convergence theorem for stochastic quasigradient methods: it covers biased and unbiased stochastic subgradients and finite-difference estimates with random step sizes, and it asserts convergence of the iterates themselves, not only of the function values or of the distance to $X^*$.
--
--   **Formalization Note** The book writes "$\gamma_0(s)$ may depend on $(x^0,\dots,x^s)$, $x^*\in X^*$"; this is read as: $\gamma_0(s)$ is a function of the history, and (6.12) holds for all $x^*\in X^*$ with the same $\gamma_0(s)$. The $x^*$-dependent error of (6.13) is covered on a bounded $X$ by $\|b^0(s)\|\operatorname{diam}X$. $X\ne\emptyset$ is implicit in the book ($X^*$ would be empty otherwise) and is stated. $x^0\in X$ is assumed because $F$ is only given on $X$ and (6.12) at $s=0$ evaluates $F(x^0)$. The last condition of (6.15) is a deterministic sum of expectations (lower Lebesgue integrals); the first two hold almost surely.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 144, Theorem 6.2 (with Eqs. (6.11), (6.12), p. 143, and (6.15), p. 144)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **Theorem 6.2** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 144): convergence with
probability 1 of the stochastic quasigradient projection method.
Minimize `F` over `X ⊆ ℝⁿ`, with optimal set `X*`. The random iterates satisfy (6.11)
`x^{s+1} = π_X[x^s - ρ_s ξ⁰(s)]`, `s = 0, 1, …`, and the random directions satisfy (6.12)
`F(x*) - F(x^s) ≥ ⟨E{ξ⁰(s) | x⁰, …, x^s}, x* - x^s⟩ + γ₀(s)` for every `x* ∈ X*`, where `ρ_s` and
`γ₀(s)` depend on `(x⁰, …, x^s)`. Assume
(a) `F` is convex and continuous on `X`,
(b) `X` is a (nonempty) convex compact set,
(c) with probability 1, `ρ_s ≥ 0` and `∑ ρ_s = ∞`, and `∑_s E{ρ_s|γ₀(s)| + ρ_s²‖ξ⁰(s)‖²} < ∞` (6.15).
Then with probability 1 the sequence `x^s` converges and its limit lies in `X*`. -/
theorem theorem_6_2_projection_method_converges {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ₀ : ℕ → Ω → ℝ)
    (hFconv : ConvexOn ℝ X F) (hFcont : ContinuousOn F X)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hx_meas : ∀ s, Measurable (x s)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ_int : ∀ s, Integrable (ξ s) μ)
    (hρ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (γ₀ s))
    (hrec : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (hqg : ∀ xstar ∈ optimalSet F X, ∀ s, ∀ᵐ ω ∂μ,
      F xstar - F (x s ω) ≥ ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ + γ₀ s ω)
    (hρ_nonneg : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hρ_div : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s ω) atTop atTop)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal (ρ s ω * |γ₀ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    ∀ᵐ ω ∂μ, ∃ xstar ∈ optimalSet F X, Tendsto (fun s => x s ω) atTop (𝓝 xstar) := by sorry

end NumStochOpt.QuasiFejer
