-- Prove2me | Theorems.Thm_GradErrors_Stochastic_lemma_6
-- name    : GradErrors.Stochastic.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:18:10.496922+00:00
-- url     : https://prove2.me/theorems/ea76da8d-6034-4db4-8298-96f37fb774b0
-- title:
--   Lemma 6, p. 640 — a.s. f(x_t) converges to a finite value or to −∞, and if not −∞ then lim sup ‖∇f(x_t)‖ ≤ δ
-- statement:
--   Assume the setting of Proposition 3. Thus $f:\mathbb R^n\to\mathbb R$ is continuously differentiable with an $L$-Lipschitz gradient; $(\Omega,\mathcal F,P)$ is a probability space with a filtration $(\mathcal F_t)$; $x_t,s_t,w_t$ are random vectors in $\mathbb R^n$ and $\gamma_t>0$ are deterministic stepsizes with
--   $$x_{t+1}=x_t+\gamma_t(s_t+w_t)$$
--   on every sample path; and
--
--   1. $x_t$ and $s_t$ are $\mathcal F_t$-measurable;
--   2. there are $c_1,c_2>0$ with $c_1\|\nabla f(x_t)\|^2\le-\nabla f(x_t)'s_t$ and $\|s_t\|\le c_2(1+\|\nabla f(x_t)\|)$ for all $t$ (on every sample path);
--   3. for all $t$, with probability 1, $E[w_t\mid\mathcal F_t]=0$ and $E[\|w_t\|^2\mid\mathcal F_t]\le A(1+\|\nabla f(x_t)\|^2)$, where $A>0$ is deterministic;
--   4. $\sum_t\gamma_t=\infty$ and $\sum_t\gamma_t^2<\infty$.
--
--   Let $\delta>0$. Then for almost every sample path, $f(x_t)$ converges to a finite value or to $-\infty$, and if $\lim_{t\to\infty}f(x_t)\ne-\infty$ then
--   $$\limsup_{t\to\infty}\|\nabla f(x_t)\|\le\delta .$$
--
--   Since $\delta>0$ is arbitrary, this lemma yields the gradient part of Proposition 3: on paths where $f(x_t)$ does not diverge to $-\infty$, $\nabla f(x_t)\to0$.
--
--   **Formalization Note** The conditional expectations in 3 are encoded through set integrals rather than Mathlib's `condExp`, which is $0$ for non-integrable functions and would make the hypotheses vacuous; the page assumes no integrability of $w_t$. Precisely: for every $\mathcal F_t$-measurable set $S$, $\int_S\|w_t\|^2\,dP\le\int_S A(1+\|\nabla f(x_t)\|^2)\,dP$ (as $[0,\infty]$-valued integrals), and $\int_S w_t\,dP=0$ whenever $\int_S\|w_t\|\,dP<\infty$. These are exactly the generalized conditional-expectation statements of the page. "$\limsup\le\delta$" is written as "for every $\delta'>\delta$, eventually $\|\nabla f(x_t)\|\le\delta'$", because $\|\nabla f(x_t)\|$ may be unbounded. Convergence to $-\infty$ is `Tendsto · atTop atBot`. $\sum_t\gamma_t=\infty$ is divergence of the partial sums to $+\infty$. The Lipschitz constant is `L : ℝ≥0`.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 640, Lemma 6 (in the setting of Proposition 3, p. 635; δ > 0 as fixed on p. 636)

import Mathlib

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

namespace GradErrors.Stochastic

theorem lemma_6 {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t ω, x (t + 1) ω = x t ω + γ t • (s t ω + w t ω))
    (hxm : ∀ t, StronglyMeasurable[ℱ t] (x t)) (hsm : ∀ t, StronglyMeasurable[ℱ t] (s t))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : ∀ t ω, c₁ * ‖gradient f (x t ω)‖ ^ 2 ≤ -⟪gradient f (x t ω), s t ω⟫_ℝ)
    (h41b : ∀ t ω, ‖s t ω‖ ≤ c₂ * (1 + ‖gradient f (x t ω)‖))
    (A : ℝ) (hA : 0 < A)
    (h42 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ ∂P < ∞ →
      ∫ ω in S, w t ω ∂P = 0)
    (h43 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S →
      ∫⁻ ω in S, ‖w t ω‖ₑ ^ 2 ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (A * (1 + ‖gradient f (x t ω)‖ ^ 2)) ∂P)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P,
      (Tendsto (fun t => f (x t ω)) atTop atBot ∨
        ∃ l : ℝ, Tendsto (fun t => f (x t ω)) atTop (𝓝 l)) ∧
      (¬ Tendsto (fun t => f (x t ω)) atTop atBot →
        ∀ δ' > δ, ∀ᶠ t in atTop, ‖gradient f (x t ω)‖ ≤ δ') := by sorry

end GradErrors.Stochastic
