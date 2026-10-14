-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_proposition_5_1_ii
-- name    : MLLangevin.ConvexA2.proposition_5_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:39.201059+00:00
-- url     : https://prove2.me/theorems/2d3c4298-e9ae-485b-9050-87772ce70a70
-- title:
--   Proposition 5.1 (ii), p. 33 — ‖X^x_{nγ} − X̄^{γ,x}_{nγ}‖₂² ≤ β₂(x)γ² uniformly in n, for γ ∈ (0, α/(2L²) ∧ 1)
-- statement:
--   Assume $(\mathbf C_\alpha)$, that $b$ is $L$-Lipschitz with $0<\alpha\le L$ and $\mathcal C^2$ with bounded partial derivatives up to order 2, and $\sigma>0$. Let $W$ be a standard $d$-dimensional Brownian motion, $x^\star\in\mathbb R^d$ and $\gamma\in(0,\frac{\alpha}{2L^2}\wedge1)$. For $x\in\mathbb R^d$ let $X^x$ be the diffusion $X^x_t=x+\int_0^tb(X^x_s)ds+\sigma W_t$ and $\bar X^{\gamma,x}$ the Euler scheme with step $\gamma$, both started at $x$ and driven by $W$. Then for every $n\ge0$ and every $x\in\mathbb R^d$,
--   $$\big\|X^x_{n\gamma}-\bar X^{\gamma,x}_{n\gamma}\big\|_2^2\le\beta_2(x)\gamma^2,$$
--   where
--   $$\frac32\beta_2(x)=\frac{2L^4}{\alpha^2}|x-x^\star|^2+\mathfrak a_0|b(x^\star)|^2+\sigma\frac{L}{\sqrt\alpha}\|\nabla b\|_{2,\infty}|x-x^\star|+\mathfrak a_1|b(x^\star)|+\mathfrak a_2d,$$
--   with $\mathfrak a_0=4\big(\frac{L^2}{\alpha^2}+\frac{L^4}{\alpha^4}\big)$, $\mathfrak a_1=\sigma(\alpha^{-1/2}+\alpha^{-3/2}L)\|\nabla b\|_{2,\infty}$ and $\mathfrak a_2=\frac{\sigma^4}{\alpha^2}\|\Delta b\|^2_{2,\infty}d^{-1}+L\|\nabla b\|_{2,\infty}\sigma^2d^{-1/2}(\alpha^{-1/2}+\alpha^{-1})+\frac{2L^4\sigma^2}{\alpha^3}$.
--
--   This is a uniform-in-time strong error bound of order one, the key estimate behind $(\mathbf H_2)$ with $\mathfrak a=2$ and $(\mathbf H_3)$ with $\delta=1$.
--
--   **Formalization Note** The $\mathcal C^2$ regularity is implicit on the page (it is needed for $\nabla b,\Delta b$) and is carried as a hypothesis, as is $\sigma>0$ (§2.4). The squared $L^2$ norm is taken in $[0,\infty]$. The statement uses one solution $X^x$ of the pathwise SDE for the given start $x$. At $d=0$ the term $\mathfrak a_2d$ is $0$, consistent with $\mathbb R^0=\{0\}$.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Proposition 5.1 (ii), pp. 32–33, with (55), p. 32

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem proposition_5_1_ii {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) (hC : MLLangevin.ConvexA1.CondC b α) (hα : 0 < α) (hαL : α ≤ L)
    (hb2 : C2Bounded b) (hσ : 0 < σ) (xs : SDEState d) (γ : ℝ) (hγ : 0 < γ)
    (hγ' : γ < min (α / (2 * L ^ 2)) 1) (n : ℕ) (x : SDEState d)
    (X : ℝ≥0 → Ω → SDEState d) (hX : IsAddSolution b σ W x X) :
    eLpNorm (fun ω => X ((n : ℝ) * γ).toNNReal ω - eulerChain b σ γ x W n ω) 2 P ^ 2 ≤
      ENNReal.ofReal (beta2 b σ α L xs x * γ ^ 2) := by sorry

end MLLangevin.ConvexA2
