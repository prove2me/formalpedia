-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_28
-- name    : NonconvexSaddle.PSGD.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:06.023622+00:00
-- url     : https://prove2.me/theorems/14235873-0994-4f30-9356-25d36d59f3a0
-- title:
--   Lemma 28 — dynamics of the coupling sequence difference: $\hat x_t=-q_h(t)-q_{sg}(t)-q_p(t)$
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ ($d\ge1$) satisfy Assumption A, let $x_0\in\mathbb R^d$, $\mathcal H=\nabla^2 f(x_0)$ and let $e_1$ be a unit minimum eigendirection of $\mathcal H$. For any step size $\eta$ and any realization of the randomness, let $\{x_t\}$ be the PSGD run from $x_0$ and $\{x'_t\}$ the coupled run of Definition 26, and $\hat x_t=x_t-x'_t$. Then for every $t\ge0$,
--   $$\hat x_t=-q_h(t)-q_{sg}(t)-q_p(t),$$
--   where
--   $$q_h(t)=\eta\sum_{\tau=0}^{t-1}(I-\eta\mathcal H)^{t-1-\tau}\Delta_\tau\hat x_\tau,\quad q_{sg}(t)=\eta\sum_{\tau=0}^{t-1}(I-\eta\mathcal H)^{t-1-\tau}\hat\zeta_\tau,\quad q_p(t)=\eta\sum_{\tau=0}^{t-1}(I-\eta\mathcal H)^{t-1-\tau}\hat\xi_\tau,$$
--   $\Delta_t=\int_0^1\nabla^2 f(\psi x_t+(1-\psi)x'_t)\,d\psi-\mathcal H$, $\hat\zeta_\tau=\zeta_\tau-\zeta'_\tau$ with $\zeta_\tau=g(x_\tau;\theta_\tau)-\nabla f(x_\tau)$ and $\zeta'_\tau=g(x'_\tau;\theta_\tau)-\nabla f(x'_\tau)$, and $\hat\xi_\tau=\xi_\tau-\xi'_\tau$.
--
--   The difference of the coupled runs splits into a Hessian-deviation term, a stochastic-gradient term and a perturbation term, each propagated by the linearized dynamics $I-\eta\mathcal H$; the perturbation term grows along the negative-curvature direction $e_1$.
--
--   **Formalization Note** The identity is deterministic: it holds for every realization, which is why no probability appears. The page's "$\hat x_t:=x_i-x'_i$" is read as $x_t-x'_t$. The eigendirection hypotheses on $e_1$ are those of Definition 26; the identity itself does not use them.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 26, Lemma 28

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 28 (Dynamics of the Coupling Sequence Difference; arXiv:1902.04811v2, App. B.3, p. 26).
Deterministic: it holds for every realization `ω` of the randomness, with `x` the PSGD run on `ω`
and `x'` the coupled run on `couple e₁ ω` (Definition 26), both started at `x₀`, and
`ℋ = ∇²f(x₀)` with unit minimum eigendirection `e₁`. -/
theorem lemma_28 (d : ℕ) (Θ : Type) (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ η : ℝ)
    (x₀ e₁ : E d) (ω : ℕ → Θ × E d) (hd : 1 ≤ d) (hA : AssumptionA f ℓ ρ) (he₁ : ‖e₁‖ = 1)
    (heig : hess f x₀ e₁ = lamMin (hess f x₀) • e₁) (t : ℕ) :
    psgd g η x₀ ω t - psgd g η x₀ (couple e₁ ω) t =
      -qh f (hess f x₀) η (psgd g η x₀ ω) (psgd g η x₀ (couple e₁ ω)) t -
        qsg f g (hess f x₀) η ω (psgd g η x₀ ω) (psgd g η x₀ (couple e₁ ω)) t -
        qp (hess f x₀) η ω (couple e₁ ω) t := by sorry

end NonconvexSaddle.PSGD
