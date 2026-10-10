-- Prove2me | Theorems.Thm_NecoaraNG_FDM_ineq_66
-- name    : NecoaraNG.FDM.ineq_66
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:34.501218+00:00
-- url     : https://prove2.me/theorems/7383a29b-3392-4c8b-bd38-4ae7b7cc57af
-- title:
--   (66), p. 30 — f(x^{k+1}) − f(x̄^{k+1}) ≤ 2(L_f + L̄_f + βL̄_f)²/κ_f · ‖x^{k+1} − x^k‖²
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex and let $f:\mathbb R^n\to\mathbb R$ be convex on $X$, differentiable at every point of $X$, with gradient Lipschitz on $X$ with constant $L_f>0$, and assume the optimal set $X^*$ of $\min_{x\in X}f(x)$ is nonempty. Assume further that $f$ has **quadratic functional growth** (22) with constant $\kappa_f>0$: for every $x\in X$ and every $\bar x=[x]_{X^*}$,
--   $$
--   f(x)-f^*\ge\frac{\kappa_f}{2}\|x-\bar x\|^2 .
--   $$
--   Let $\beta,L,\bar L_f>0$ and let $(x^k)$, $(e^k)$, $(\alpha_k)$ be a run of the feasible descent method (FDM). Then for every $k\ge0$ and every $\bar x^{k+1}=[x^{k+1}]_{X^*}$,
--   $$
--   f(x^{k+1})-f(\bar x^{k+1})\ \le\ \frac{2(L_f+\bar L_f+\beta\bar L_f)^2}{\kappa_f}\,\|x^{k+1}-x^k\|^2 .
--   $$
--
--   The bound controls the optimality gap by the squared step length; combined with the sufficient decrease of (FDM) it gives the one-step contraction behind Theorem 15.
--
--   **Formalization Note** $f$ belongs to the class $\mathcal F_{L_f,\kappa_f}(X)$ of the paper through three separate hypotheses: convexity on $X$, the Lipschitz bound (1) and (22). $[x]_{X^*}$ is the predicate `IsNearest (optSet X f)`.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 30, proof of Theorem 15, (66)

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

namespace NecoaraNG.FDM

open scoped InnerProductSpace

/-- (66), proof of Theorem 15, p. 30: under quadratic functional growth (22) with constant `κ`,
for every `k` and `x̄^{k+1} = [x^{k+1}]_{X*}`,
`f(x^{k+1}) - f(x̄^{k+1}) ≤ 2 (L_f + L̄_f + β L̄_f)² / κ · ‖x^{k+1} - x^k‖²`. -/
theorem ineq_66 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLpos : 0 < L) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x (k + 1)) xbar →
      f (x (k + 1)) - f xbar ≤
        2 * (Lf + Lbar + β * Lbar) ^ 2 / κ * ‖x (k + 1) - x k‖ ^ 2 := by sorry

end NecoaraNG.FDM
