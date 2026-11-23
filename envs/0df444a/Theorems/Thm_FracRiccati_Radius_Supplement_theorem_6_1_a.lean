-- Prove2me | Theorems.Thm_FracRiccati_Radius_Supplement_theorem_6_1_a
-- name    : FracRiccati.Radius.Supplement.theorem_6_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:56:58.073225+00:00
-- url     : https://prove2.me/theorems/63f63a7d-4b39-44a0-9495-c1caad50e0a1
-- title:
--   Theorem 6.1(a) — normally convergent double-series integral solution and all valuation cases
-- statement:
--   Let $1/2<\alpha<1$, $\lambda\ne0$, and $\mu,\nu,u\in\mathbb C$, allowing zero initial data and zero $\nu$. Let $a_{k,\ell}$ be the recursively constructed coefficients (6.37)–(6.38) with $v=0$. There exists a real $R>0$ such that
--   $$\psi(t)=\sum_{(k,\ell)\in\mathbb N^2}a_{k,\ell}t^{\alpha k-\ell}=\sum_{\ell\ge0}\sum_{k\ge0}a_{k,\ell}t^{\alpha k-\ell}\qquad(0<t<R)$$
--   is normally convergent on every compact interval in $(0,R)$, pointwise absolutely summable, and solves (2.12) with its weighted kernel integrable. Write $k(\ell)$ for the least nonzero positive first index, with $+\infty$ for a zero level. All the valuation conclusions are retained:
--   $$k(\ell)\ge (2\ell-1)\vee1;\qquad \nu\ne0,\ u\ne0\ \Longrightarrow\ k(\ell)=(2\ell-1)\vee1.$$
--   If $\nu=0$ then $k(0)=+\infty$; if $u=0$ then $k(\ell)=+\infty$ for every $\ell\ge1$. The theorem also states the two initial coefficients, vanishing of $a_{1,\ell}$ for $\ell\ge2$, vanishing of $a^{*2}_{1,\ell}$, and the recurrence for every $k\ge2$. This gives an actual solution built from the paper's data, rather than an arbitrary array with the desired properties assumed.
--
--   Differences from the source:
--   - encoding: lambda nonzero is a standing assumption → lambda nonzero is bound explicitly, while nu and u may vanish; reason: Assumption 3.1 applies to lambda, and Theorem 6.1 explicitly overrides its nu nonzero clause
--   - reading: the preamble says [0,R) but its formula says 0<t<R → all time assertions are on (0,R); reason: the term u t^(alpha-1) is singular at zero; the displayed formula (6.36) supplies the intended interval
--   - encoding: a solution of the fractional equation → a solution of the integral form with an integrable weighted kernel; reason: Section 6 explicitly chooses (2.12)-(2.13); integrability prevents the Bochner zero default from satisfying a spurious equation
--   - encoding: normal convergence on compact intervals and iterated sums → summable uniform norm bounds for pair terms, absolute summability, and equality with the iterated sum; reason: these are equivalent descriptions of normal convergence; zero terms extend the index set below the valuation
--   - reading: the recursion is written only above the valuation → the recursion computes all rows k>=2 and zero coefficients below the valuation; reason: this removes circularity without adding a premise; in case (a) every nonzero prefactor has positive Gamma arguments
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 24, Theorem 6.1(a)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_IntegralSolution
import Definitions.Def_FracRiccati_Radius_Supplement_DoubleSeries

namespace FracRiccati.Radius.Supplement

theorem theorem_6_1_a (α : ℝ) (lam mu nu u : ℂ)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hlam : lam ≠ 0) :
    let a := doubleCoeff α lam mu nu u 0
    (∃ R : ℝ, 0 < R ∧ NormallyConvergent α a R ∧
      IsIntegralSolution α lam mu nu u 0 R (doublePsi α a) ∧
      ∀ t ∈ Set.Ioo 0 R,
        Summable (fun i : ℕ × ℕ => doubleTerm α a i t) ∧
        doublePsi α a t = ∑' ℓ : ℕ, ∑' k : ℕ, doubleTerm α a (k, ℓ) t) ∧
    (∀ ℓ : ℕ, ((max (2 * ℓ - 1) 1 : ℕ) : ℕ∞) ≤ valuation a ℓ) ∧
    (nu ≠ 0 → u ≠ 0 → ∀ ℓ : ℕ,
      valuation a ℓ = ((max (2 * ℓ - 1) 1 : ℕ) : ℕ∞)) ∧
    (nu = 0 → valuation a 0 = ⊤) ∧
    (u = 0 → ∀ ℓ : ℕ, 1 ≤ ℓ → valuation a ℓ = ⊤) ∧
    a 1 0 = nu / (Real.Gamma (α + 1) : ℂ) ∧
    a 1 1 = u / (Real.Gamma α : ℂ) ∧
    (∀ ℓ : ℕ, 2 ≤ ℓ → a 1 ℓ = 0) ∧
    (∀ ℓ : ℕ, doubleConvolution a 1 ℓ = 0) ∧
    (∀ k ℓ : ℕ, 2 ≤ k → a k ℓ =
      (mu * a (k - 1) ℓ + lam * doubleConvolution a (k - 1) ℓ) *
        ((Real.Gamma (α * ((k - 1 : ℕ) : ℝ) - (ℓ : ℝ) + 1) /
          Real.Gamma (α * (k : ℝ) - (ℓ : ℝ) + 1) : ℝ) : ℂ)) := by sorry

end FracRiccati.Radius.Supplement
