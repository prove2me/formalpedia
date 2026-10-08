-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_ch18_theorem_2_adaptive_sqg
-- name    : NumStochOpt.Stepsize.ch18_theorem_2_adaptive_sqg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:24:38.517905+00:00
-- url     : https://prove2.me/theorems/3d1766e0-93d5-4222-8e56-18b700def9a1
-- title:
--   Ch. 18 Theorem 2 — the adaptive SQG method (18.2), (18.5): $\limsup(F(\bar x^s)-\min_XF)\le\bar bC_1$ a.s.
-- statement:
--   Let $F$ be a convex, possibly nonsmooth, function on an open convex set $U\subseteq\mathbb R^n$ containing the convex compact set $X$, let $\partial F(x)$ be its set of subgradients at $x$, and let $x^*$ minimize $F$ on $X$. Let
--   $$
--   C_1=\max_{x,y\in X}\|x-y\|\qquad(18.14).
--   $$
--   On a probability space, run the adaptive stochastic quasigradient method with $a>1$, $\delta>0$, a fixed $\rho_0>0$ and a starting point $x^0\in X$:
--   $$
--   x^{s+1}=\pi_X(x^s-\rho_s\xi^s)\quad(18.2),\qquad \rho_{s+1}=\rho_s\,a^{\langle\xi^{s+1},x^s-x^{s+1}\rangle-\delta\rho_s}\quad(18.5),
--   $$
--   where $E(\xi^s\mid B_s)=F_x(x^s)+b^s$ with $F_x(x^s)\in\partial F(x^s)$ and $B_s$ the $\sigma$-algebra induced by $(x^0,\dots,x^s,\xi^0,\dots,\xi^{s-1})$. Assume, almost surely,
--
--   1. $\sup_s\|\xi^s\|<C_2$ (18.15);
--   2. $\limsup_{s\to\infty}\|b^s\|\le\bar b$ (18.16);
--   3. $\delta>C_2\,\limsup_{s\to\infty}\inf_{h\in\partial F(x^s)}\|\xi^s-h\|$ (18.17).
--
--   Then, with the weighted averages $\bar x^s=\sum_{\ell=0}^s\rho_\ell x^\ell/\sum_{\ell=0}^s\rho_\ell$ of (18.6),
--   $$
--   \limsup_{s\to\infty}\Big(F(\bar x^s)-\min_{x\in X}F(x)\Big)\le\bar b\,C_1\quad\text{a.s.};
--   $$
--   and if $b^s\to0$ a.s., then $F(\bar x^s)\to\min_{x\in X}F(x)$ a.s. and almost surely every accumulation point of $\bar x^s$ is a solution of problem (18.1).
--
--   The theorem is the convergence result for the adaptive stepsize rule of the chapter: the stepsize grows when successive quasigradients point the same way and shrinks when they point in opposite directions, and no square summability of the stepsizes is required. The book's proof is an outline that checks the hypotheses of Theorem 1.
--
--   **Formalization Note** (a) The page prints (18.17) with $C_1$; the proof's estimate (through (18.18)) gives the exponent $(C_2C_s-\delta)\rho_s$, and only $C_2$ makes the condition invariant under rescaling of $\mathbb R^n$, so $C_2$ is stated. (b) The stepsize rule is the second form of (18.5); the first form, $\rho_sa^{\rho_s\langle\xi^{s+1},\xi^s\rangle-\delta\rho_s}$, agrees with it only when the projection is inactive, and the proof uses the second. (c) The page's "$F(x^s)-\min z\in XF(x)\to0$" is read as $F(\bar x^s)-\min_{x\in X}F(x)\to0$, the $\bar b=0$ case of the preceding line. (d) $\rho_0$ is a deterministic positive number; the conditioning $\sigma$-algebra is the $B_s$ of Theorem 1, condition (1). (e) $\sup_s\|\xi^s\|<C_2$ is written as a bound $c<C_2$ on all $\|\xi^s\|$; each $\limsup$ is written out as an eventual inequality up to every $\varepsilon>0$ (or, in (18.17), up to a bound $L$ with $C_2L<\delta$), which avoids Lean's junk value of a real $\limsup$. (f) The page switches between $f$ and $F$; they are the same function.
-- source:
--   S. Uryasev, "Adaptive Stochastic Quasigradient Procedures", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 18, p. 377, Theorem 2, Eqs. (18.14)–(18.17), with (18.2) p. 373, (18.5), (18.6) p. 375

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.Stepsize

/-- **Theorem 2** of Uryasev, Ch. 18 of Ermoliev & Wets (1988), p. 377: Cesàro convergence of the
adaptive stochastic quasigradient method (18.2), (18.5).

`F` is convex (possibly nonsmooth) on an open convex `U ⊆ ℝⁿ` containing the convex compact
`X`, with diameter `C₁` (18.14); `∂F(x)` is its set of subgradients and `x*` a minimizer of `F`
on `X`. The process is `x⁰ ∈ X`, `x^{s+1} = π_X(x^s - ρ_s ξ^s)` (18.2) and
`ρ_{s+1} = ρ_s a^{⟨ξ^{s+1}, x^s - x^{s+1}⟩ - δ ρ_s}` (18.5, second form), with `a > 1`, `δ > 0`
and a deterministic `ρ₀ > 0`. The direction is a stochastic quasigradient,
`E(ξ^s | B_s) = F_x(x^s) + b^s` with `F_x(x^s) ∈ ∂F(x^s)` and `B_s` the σ-algebra induced by
`(x⁰, …, x^s, ξ⁰, …, ξ^{s-1})`. Assume
(18.15) `sup_s ‖ξ^s‖ < C₂` a.s., (18.16) `limsup_s ‖b^s‖ ≤ b̄` a.s., and
(18.17) `δ > C₂ · limsup_s inf_{h ∈ ∂F(x^s)} ‖ξ^s - h‖` a.s. (the page prints `C₁`; the proof's
estimate, through (18.18), needs the bound `C₂` of (18.15)).
Then, with `x̄^s` the weighted average (18.6),
1. `limsup_s (F(x̄^s) - min_X F) ≤ b̄ C₁` a.s., and
2. if `b^s → 0` a.s., then a.s. `F(x̄^s) → min_X F` and every accumulation point of `x̄^s` is a
   solution of problem (18.1), i.e. a minimizer of `F` on `X`.
Each `limsup` bound is written out as an eventual bound up to every `ε > 0`. -/
theorem ch18_theorem_2_adaptive_sqg {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (U X : Set (EuclideanSpace ℝ (Fin n)))
    (xstar : EuclideanSpace ℝ (Fin n)) (a δ ρ₀ C₁ C₂ bbar : ℝ)
    (x ξ g b : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ)
    (hU_open : IsOpen U) (hU_conv : Convex ℝ U) (hXU : X ⊆ U)
    (hX_conv : Convex ℝ X) (hX_cpt : IsCompact X) (hF_conv : ConvexOn ℝ U F)
    (hxstar : xstar ∈ X ∧ ∀ y ∈ X, F xstar ≤ F y)
    -- the process (18.2) with the stepsize rule (18.5)
    (ha : 1 < a) (hδ : 0 < δ) (hρ₀ : 0 < ρ₀)
    (hx_meas : ∀ s, Measurable (x s)) (hξ_meas : ∀ s, Measurable (ξ s))
    (hx0 : ∀ ω, x 0 ω ∈ X) (hρ0 : ∀ ω, ρ 0 ω = ρ₀)
    (hrec : ∀ s ω, x (s + 1) ω = NumStochOpt.QuasiFejer.projX X (x s ω - ρ s ω • ξ s ω))
    (hrule : ∀ s ω, ρ (s + 1) ω =
      ρ s ω * a ^ (⟪ξ (s + 1) ω, x s ω - x (s + 1) ω⟫_ℝ - δ * ρ s ω))
    -- the stochastic quasigradient condition
    (hg : ∀ s, ∀ᵐ ω ∂μ, g s ω ∈ subdiffOn U F (x s ω))
    (hqg : ∀ s, μ[ξ s | histSigma x ξ s s] =ᵐ[μ] fun ω => g s ω + b s ω)
    -- (18.14)
    (h1814 : Metric.diam X = C₁)
    -- (18.15)
    (h1815 : ∀ᵐ ω ∂μ, ∃ c < C₂, ∀ s, ‖ξ s ω‖ ≤ c)
    -- (18.16)
    (h1816 : ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ s in atTop, ‖b s ω‖ ≤ bbar + ε)
    -- (18.17)
    (h1817 : ∀ᵐ ω ∂μ, ∃ L, C₂ * L < δ ∧
      ∀ᶠ s in atTop, Metric.infDist (ξ s ω) (subdiffOn U F (x s ω)) ≤ L) :
    (∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ s in atTop,
      F (weightedAvg (fun ℓ => ρ ℓ ω) (fun ℓ => x ℓ ω) s) - F xstar ≤ bbar * C₁ + ε) ∧
    ((∀ᵐ ω ∂μ, Tendsto (fun s => b s ω) atTop (𝓝 0)) →
      ∀ᵐ ω ∂μ,
        Tendsto (fun s => F (weightedAvg (fun ℓ => ρ ℓ ω) (fun ℓ => x ℓ ω) s)) atTop
          (𝓝 (F xstar)) ∧
        ∀ z, MapClusterPt z atTop (fun s => weightedAvg (fun ℓ => ρ ℓ ω) (fun ℓ => x ℓ ω) s) →
          z ∈ X ∧ ∀ y ∈ X, F z ≤ F y) := by sorry

end NumStochOpt.Stepsize
