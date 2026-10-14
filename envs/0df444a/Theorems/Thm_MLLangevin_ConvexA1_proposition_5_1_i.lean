-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_proposition_5_1_i
-- name    : MLLangevin.ConvexA1.proposition_5_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:11.461955+00:00
-- url     : https://prove2.me/theorems/8534591d-6f18-4a3c-8a13-80d1c24359d5
-- title:
--   Proposition 5.1 (i), pp. 32–33 — ‖X^x_{nγ} − X̄^{γ,x}_{nγ}‖₂² ≤ β₁(x)γ for every n
-- statement:
--   Let $b$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$ with $0<\alpha\le L$, $\sigma>0$, $W$ a standard $d$-dimensional Brownian motion, $x^\star\in\mathbb R^d$ and $\gamma\in(0,\frac\alpha{2L^2}\wedge1)$. For $x\in\mathbb R^d$ let $X^x$ solve $X^x_t=x+\int_0^tb(X^x_s)ds+\sigma W_t$ and let $\bar X^{\gamma,x}$ be the Euler scheme with step $\gamma$ started at $x$, driven by the same $W$. Then for every $n\ge0$,
--   $$\big\|X^x_{n\gamma}-\bar X^{\gamma,x}_{n\gamma}\big\|_2^2\le\beta_1(x)\,\gamma,\qquad\beta_1(x)=\frac{L^2}\alpha|x-x^\star|^2+2|b(x^\star)|^2\Big(\frac1\alpha+\frac{L^2}{\alpha^3}\Big)+\frac{3L^2\sigma^2d}{\alpha^2}.$$
--
--   The bound is uniform in $n$: the strong error does not accumulate over an infinite horizon. It yields both the $L^2$-confluence $(\mathbf H_2)$ with $\mathfrak a=1$ and the bias bound $(\mathbf H_3)$ with $\delta=\frac12$.
--
--   **Formalization Note** $\|\cdot\|_2^2$ is `eLpNorm … 2 P ^ 2` in $[0,\infty]$; $\gamma<\frac\alpha{2L^2}\wedge1$ is strict, as on the page.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Proposition 5.1 (i), pp. 32–33, with (55)

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Proposition 5.1 (i), pp. 32–33: the strong error of the additive Euler scheme at grid
times, `‖X^x_{nγ} − X̄^{γ,x}_{nγ}‖₂² ≤ β₁(x) γ`, uniformly in `n`. -/
theorem proposition_5_1_i {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (hC : CondC b α) (hα : 0 < α) (hαL : α ≤ L) (hσ : 0 < σ)
    (xs x : SDEState d) (X : ℝ≥0 → Ω → SDEState d) (hX : IsAddSolution b σ W x X)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ < min (α / (2 * L ^ 2)) 1) (n : ℕ) :
    eLpNorm (fun ω => X (gridTime n γ) ω - eulerChain b σ γ x W n ω) 2 P ^ 2 ≤
      ENNReal.ofReal (beta1 b σ α L xs x * γ) := by sorry

end MLLangevin.ConvexA1
