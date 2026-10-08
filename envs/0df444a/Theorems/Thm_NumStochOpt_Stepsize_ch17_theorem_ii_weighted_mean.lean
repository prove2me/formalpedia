-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_ch17_theorem_ii_weighted_mean
-- name    : NumStochOpt.Stepsize.ch17_theorem_ii_weighted_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:23:59.673574+00:00
-- url     : https://prove2.me/theorems/a0f8208c-1a1d-4a2c-ae3e-8327fef5fec1
-- title:
--   Ch. 17 Theorem (ii) — the weighted mean $\bar X_n\to x^*$ a.s. when $\rho_n\to0$, $\sum\rho_n=\infty$ (Mirzoakhmedov–Uryasev)
-- statement:
--   Take the setting of part (i): $f(x)=E_P\,q(x,\cdot)$ minimized over a closed convex $S\subseteq\mathbb R^k$, with $q(\cdot,\xi)$ $L^1(P)$-differentiable with derivative $\nabla q(x,\xi)$ (17.3), unique minimizer $x^*$, i.i.d. $\xi_0,\xi_1,\dots$ with law $P$, $\mathcal F_n=\sigma(\xi_0,\dots,\xi_{n-1})$, $X_0=x_0$ fixed and
--   $$
--   X_{n+1}=\Pi_S\big(X_n-\rho_n\nabla q(X_n,\xi_n)\big).
--   $$
--   Assume (iii) $E\|\nabla q(x,\xi)-\nabla f(x)\|^2\le C$ for all $x$, and (iv) $\rho_n\ge0$ almost surely with $\rho_n$ $\mathcal F_n$-measurable. If moreover $f$ is convex and $S$ is bounded, then
--   $$
--   \rho_n\to0\ \text{a.s.}\quad\text{and}\quad\sum_n\rho_n=\infty\ \text{a.s.}\quad\Longrightarrow\quad\bar X_n=\frac{\sum_{i=0}^n\rho_iX_i}{\sum_{i=0}^n\rho_i}\to x^*\ \text{a.s.}
--   $$
--
--   Compared with part (i), the square summability $\sum\rho_n^2<\infty$ and the growth assumptions (i), (ii) on $\nabla f$ are dropped, at the price of convexity, a bounded feasible set, and convergence of the weighted mean rather than of the iterates themselves. Chapter 18 generalizes this result.
--
--   **Formalization Note** "Under the above conditions" is printed only for part (i); part (ii) is stated with the hypotheses it names (convexity of $f$ on $\mathbb R^k$, bounded $S$, $\rho_n\to0$, $\sum\rho_n=\infty$) together with the standing ones (17.1)–(17.4a), (iii), (iv) and uniqueness of $x^*$. The book's weighted mean runs over $i=1,\dots,n$ with the process started at $X_1$; with the shift to $0$-based indexing it runs over $i=0,\dots,n$. The mean is $0$ while $\sum_{i\le n}\rho_i=0$, which does not affect the limit.
-- source:
--   G. Ch. Pflug, "Stepsize Rules, Stopping Times and their Implementation in Stochastic Quasigradient Algorithms", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 17, p. 357, Theorem (ii) (Mirzoakhmedov and Uryasev [14]), with the assumptions on p. 356

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.Stepsize

/-- **Theorem (ii)** of Pflug, Ch. 17 of Ermoliev & Wets (1988), p. 357 (Mirzoakhmedov and
Uryasev): almost sure convergence of the weighted mean of the stochastic quasigradient projection
method (17.4), (17.4a) when the stepsizes tend to zero but need not be square summable.

Same setting as part (i): `f(x) = E_P q(x, ·)` with `q(·, ξ)` `L¹(P)`-differentiable with
derivative `∇q(x, ξ)` (17.3); `X_{n+1} = Π_S(X_n - ρ_n ∇q(X_n, ξ_n))` with `ξ₀, ξ₁, …` i.i.d. with
law `P` (indices shifted by one against the page); `x*` the unique minimizer of `f` on `S`;
(iii) `E‖∇q(x, ξ) - ∇f(x)‖² ≤ C`; (iv) `ρ_n ≥ 0`, `ρ_n` measurable w.r.t. `σ(ξ₀, …, ξ_{n-1})`.
If moreover `f` is convex and `S` is bounded, then `ρ_n → 0` a.s. and `∑ ρ_n = ∞` a.s. imply
`X̄_n → x*` a.s., where `X̄_n = ∑_{i ≤ n} ρ_i X_i / ∑_{i ≤ n} ρ_i` is the weighted mean.
Assumptions (i) and (ii) of part (i) are not used. -/
theorem ch17_theorem_ii_weighted_mean {k : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace Ω]
    (P : Measure Ξ) [IsProbabilityMeasure P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : EuclideanSpace ℝ (Fin k) → Ξ → ℝ)
    (G : EuclideanSpace ℝ (Fin k) → Ξ → EuclideanSpace ℝ (Fin k))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (S : Set (EuclideanSpace ℝ (Fin k)))
    (xstar x₀ : EuclideanSpace ℝ (Fin k)) (C : ℝ)
    (ξ : ℕ → Ω → Ξ) (ρ : ℕ → Ω → ℝ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    -- the problem (17.1)–(17.3), case (a)
    (hq_int : ∀ x, Integrable (q x) P)
    (hf : ∀ x, f x = ∫ ξ', q x ξ' ∂P)
    (hG_meas : Measurable (Function.uncurry G))
    (hG_int : ∀ x, Integrable (G x) P)
    (hL1diff : ∀ x, (fun y => ∫ ξ', |q y ξ' - q x ξ' - ⟪y - x, G x ξ'⟫_ℝ| ∂P) =o[𝓝 x]
      (fun y => y - x))
    (hS_closed : IsClosed S) (hS_conv : Convex ℝ S)
    (hxstar : xstar ∈ S ∧ ∀ y ∈ S, f xstar ≤ f y)
    (hunique : ∀ y ∈ S, (∀ z ∈ S, f y ≤ f z) → y = xstar)
    -- the additional hypotheses of part (ii)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hS_bdd : Bornology.IsBounded S)
    -- assumptions (iii), (iv)
    (hiii : ∀ x, ∫⁻ ξ', ENNReal.ofReal (‖G x ξ' - ∫ η, G x η ∂P‖ ^ 2) ∂P ≤ ENNReal.ofReal C)
    (hiv_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ ρ n ω)
    (hiv_meas : ∀ n, Measurable[noiseSigma ξ n] (ρ n))
    -- the i.i.d. sequence ξ₀, ξ₁, … with distribution P
    (hξ_meas : ∀ n, Measurable (ξ n))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_law : ∀ n, μ.map (ξ n) = P)
    -- the recursion (17.4), (17.4a)
    (hX0 : ∀ ω, X 0 ω = x₀)
    (hrec : ∀ n ω, X (n + 1) ω = NumStochOpt.QuasiFejer.projX S (X n ω - ρ n ω • G (X n ω) (ξ n ω))) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => ρ n ω) atTop (𝓝 0)) →
    (∀ᵐ ω ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n ω) atTop atTop) →
    ∀ᵐ ω ∂μ, Tendsto (fun n => weightedAvg (fun i => ρ i ω) (fun i => X i ω) n) atTop
      (𝓝 xstar) := by sorry

end NumStochOpt.Stepsize
