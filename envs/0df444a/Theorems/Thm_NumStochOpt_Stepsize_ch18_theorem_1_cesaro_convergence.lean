-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_ch18_theorem_1_cesaro_convergence
-- name    : NumStochOpt.Stepsize.ch18_theorem_1_cesaro_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:23:49.930545+00:00
-- url     : https://prove2.me/theorems/ac119dad-9330-444c-a1e6-dad51f8d2836
-- title:
--   Ch. 18 Theorem 1 — $\limsup F(\bar x^s)-F(x^*)\le\bar bC_1$ a.s. for SQG with $\rho_s\to0$, $\sum\rho_s=\infty$
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex, closed and bounded with diameter
--   $$
--   C_1=\max_{x,y\in X}\|x-y\|\qquad(18.7),
--   $$
--   let $F$ be convex on $X$ and $x^*\in X$ a minimizer of $F$ on $X$. On a probability space $(\Omega,\mathcal A,P)$ let $x^0\in X$ and
--   $$
--   x^{s+1}=\pi_X(x^s-\rho_s\xi^s),\qquad s=0,1,\dots\qquad(18.2),
--   $$
--   where $\xi^s$ is a stochastic quasigradient: $E(\xi^s\mid B_s)=F_x(x^s)+b^s$, with $F_x(x^s)$ a subgradient of $F$ at $x^s$ (relative to $X$) and $B_s$ the $\sigma$-algebra induced by $(x^0,\dots,x^s,\xi^0,\dots,\xi^{s-1})$. Assume
--
--   1. $E\|\xi^s-F_x(x^s)-b^s\|^2\le C_2^2$ for all $s$ (18.8);
--   2. $\limsup_{s\to\infty}\|b^s\|\le\bar b$ a.s. (18.9);
--   3. $\rho_s>0$ a.s. (18.10), $E\rho_s^2<\infty$ (18.11), $\rho_s\to0$ a.s. (18.12), $\sum_{s=0}^\infty\rho_s=\infty$ a.s. (18.13);
--   4. either (1) $\rho_s$ is measurable with respect to $B_s$, or (2) $\rho_s\rho_{s-1}^{-1}\to1$ a.s. and $\rho_s$ is measurable with respect to the $\sigma$-algebra induced by $(x^0,\dots,x^s,\xi^0,\dots,\xi^s)$.
--
--   Then, with $\bar x^s=\sum_{\ell=0}^s\rho_\ell x^\ell/\sum_{\ell=0}^s\rho_\ell$ (18.6),
--   $$
--   \limsup_{s\to\infty}F(\bar x^s)-F(x^*)\le\bar b\,C_1\quad\text{a.s.}
--   $$
--
--   The theorem trades the classical $\sum\rho_s^2<\infty$ for Cesàro (weighted-average) convergence; this is what makes adaptive stepsize rules, whose square summability is hard to verify, analysable. Condition (2) admits stepsizes that depend on the current direction $\xi^s$, as the adaptive rule (18.5) does. The book cites the proof from its reference [7].
--
--   **Formalization Note** Two misprints on p. 376 are read as follows: (18.8) prints $F_s(x^s)$ for the quasigradient $F_x(x^s)$ of §18.2, and (18.11) prints $E\rho_s^s<\infty$, read as $E\rho_s^2<\infty$. The conditioning $\sigma$-algebra of the quasigradient condition is the $B_s$ that condition (1) names (§18.2 describes it as "the process history"). Subgradients are taken relative to $X$ (the only domain of $F$ here); for a differentiable $F$ on a neighbourhood the gradient is one. The start $x^0\in X$ is added so that $F(\bar x^s)$ is defined. The $\limsup$ inequalities are written out as "for every $\varepsilon>0$, eventually $\dots\le\dots+\varepsilon$", which avoids Lean's junk value of a real $\limsup$ of an unbounded sequence; $E\|\cdot\|^2$ is a lower Lebesgue integral.
-- source:
--   S. Uryasev, "Adaptive Stochastic Quasigradient Procedures", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 18, p. 376, Theorem 1 (cited from [7]), Eqs. (18.7)–(18.13), with (18.2) p. 373 and (18.6) p. 375

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.Stepsize

/-- **Theorem 1** of Uryasev, Ch. 18 of Ermoliev & Wets (1988), p. 376 (cited from [7]): Cesàro
convergence of the stochastic quasigradient projection method (18.2) with random stepsizes.

`F` is convex on a convex closed bounded `X ⊆ ℝⁿ` with diameter `C₁` (18.7), `x* ∈ X` minimizes
`F` on `X`, and `x^{s+1} = π_X(x^s - ρ_s ξ^s)` with `x⁰ ∈ X`. The direction `ξ^s` is a stochastic
quasigradient: `E(ξ^s | B_s) = F_x(x^s) + b^s` with `F_x(x^s)` a subgradient of `F` at `x^s`
and `B_s` the σ-algebra induced by `(x⁰, …, x^s, ξ⁰, …, ξ^{s-1})`. Assume
(18.8) `E‖ξ^s - F_x(x^s) - b^s‖² ≤ C₂²`, (18.9) `limsup ‖b^s‖ ≤ b̄`, (18.10) `ρ_s > 0` a.s.,
(18.11) `E ρ_s² < ∞` (the page prints `Eρ_s^s`), (18.12) `ρ_s → 0` a.s., (18.13) `∑ ρ_s = ∞` a.s.,
and one of: (1) `ρ_s` is measurable w.r.t. `σ(x⁰, …, x^s, ξ⁰, …, ξ^{s-1})`; (2) `ρ_s/ρ_{s-1} → 1`
a.s. and `ρ_s` is measurable w.r.t. `σ(x⁰, …, x^s, ξ⁰, …, ξ^s)`.
Then `limsup_s F(x̄^s) - F(x*) ≤ b̄ C₁` a.s., where `x̄^s` is the weighted average (18.6); the
`limsup` is written out as: for every `ε > 0`, eventually `F(x̄^s) - F(x*) ≤ b̄ C₁ + ε`. -/
theorem ch18_theorem_1_cesaro_convergence {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (xstar : EuclideanSpace ℝ (Fin n)) (C₁ C₂ bbar : ℝ)
    (x ξ g b : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ)
    (hX_conv : Convex ℝ X) (hX_closed : IsClosed X) (hX_bdd : Bornology.IsBounded X)
    (hF_conv : ConvexOn ℝ X F)
    (hxstar : xstar ∈ X ∧ ∀ y ∈ X, F xstar ≤ F y)
    -- the process (18.2) and the stochastic quasigradient condition
    (hx_meas : ∀ s, Measurable (x s)) (hξ_meas : ∀ s, Measurable (ξ s))
    (hξ_int : ∀ s, Integrable (ξ s) μ)
    (hx0 : ∀ ω, x 0 ω ∈ X)
    (hrec : ∀ s ω, x (s + 1) ω = NumStochOpt.QuasiFejer.projX X (x s ω - ρ s ω • ξ s ω))
    (hg : ∀ s, ∀ᵐ ω ∂μ, g s ω ∈ subdiffOn X F (x s ω))
    (hqg : ∀ s, μ[ξ s | histSigma x ξ s s] =ᵐ[μ] fun ω => g s ω + b s ω)
    -- (18.7)
    (h187 : Metric.diam X = C₁)
    -- (18.8)
    (h188 : ∀ s, ∫⁻ ω, ENNReal.ofReal (‖ξ s ω - g s ω - b s ω‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₂ ^ 2))
    -- (18.9)
    (h189 : ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ s in atTop, ‖b s ω‖ ≤ bbar + ε)
    -- (18.10)
    (h1810 : ∀ s, ∀ᵐ ω ∂μ, 0 < ρ s ω)
    -- (18.11)
    (h1811 : ∀ s, Integrable (fun ω => ρ s ω ^ 2) μ)
    -- (18.12)
    (h1812 : ∀ᵐ ω ∂μ, Tendsto (fun s => ρ s ω) atTop (𝓝 0))
    -- (18.13)
    (h1813 : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s ω) atTop atTop)
    -- condition (1) or condition (2)
    (hregime : (∀ s, Measurable[histSigma x ξ s s] (ρ s)) ∨
      ((∀ᵐ ω ∂μ, Tendsto (fun s => ρ (s + 1) ω / ρ s ω) atTop (𝓝 1)) ∧
        ∀ s, Measurable[histSigma x ξ s (s + 1)] (ρ s))) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ s in atTop,
      F (weightedAvg (fun ℓ => ρ ℓ ω) (fun ℓ => x ℓ ω) s) - F xstar ≤ bbar * C₁ + ε := by sorry

end NumStochOpt.Stepsize
