-- Prove2me | Theorems.Thm_NecoaraNG_FDM_gap_le_product
-- name    : NecoaraNG.FDM.gap_le_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:47.725464+00:00
-- url     : https://prove2.me/theorems/9406ff15-3c96-4450-b064-50e26bb38263
-- title:
--   Proof of Theorem 15, p. 29 — f(x^{k+1}) − f(x̄^{k+1}) ≤ (L_f + L̄_f + βL̄_f)‖x^{k+1} − x^k‖‖x^{k+1} − x̄^{k+1}‖
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex and let $f:\mathbb R^n\to\mathbb R$ be convex on $X$, differentiable at every point of $X$, with gradient Lipschitz on $X$ with constant $L_f>0$:
--   $$
--   \|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|\qquad\text{for all } x,y\in X ,
--   $$
--   and assume the problem $\min_{x\in X}f(x)$ has a minimizer, so that the optimal set $X^*$ is nonempty. Let $\beta,L,\bar L_f>0$ and let $(x^k)$, $(e^k)$, $(\alpha_k)$ be a run of the feasible descent method (FDM): $x^0\in X$ and, for every $k\ge0$, $x^{k+1}=[x^k-\alpha_k\nabla f(x^k)+e^k]_X$, $\|e^k\|\le\beta\|x^{k+1}-x^k\|$, $f(x^{k+1})\le f(x^k)-\frac L2\|x^{k+1}-x^k\|^2$ and $\alpha_k\ge\bar L_f^{-1}$.
--
--   Then for every $k\ge0$ and every nearest point $\bar x^{k+1}=[x^{k+1}]_{X^*}$,
--   $$
--   f(x^{k+1})-f(\bar x^{k+1})\ \le\ (L_f+\bar L_f+\beta\bar L_f)\,\|x^{k+1}-x^k\|\,\|x^{k+1}-\bar x^{k+1}\| .
--   $$
--
--   The inequality bounds the optimality gap after one step by the length of that step times the distance to the optimal set; together with quadratic functional growth it yields (66).
--
--   **Formalization Note** The page derives this inside the proof of Theorem 15, where $f\in\mathcal F_{L_f,\kappa_f}$; the growth condition (22) is not used in this step and is not a hypothesis here. $[x]_{X^*}$ is the predicate `IsNearest (optSet X f)`, and the statement holds for every nearest point.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 29, proof of Theorem 15, display chain after (65)

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

namespace NecoaraNG.FDM

open scoped InnerProductSpace

/-- Proof of Theorem 15, chain before (66), p. 29: for every `k` and `x̄^{k+1} = [x^{k+1}]_{X*}`,
`f(x^{k+1}) - f(x̄^{k+1}) ≤ (L_f + L̄_f + β L̄_f) ‖x^{k+1} - x^k‖ ‖x^{k+1} - x̄^{k+1}‖`. -/
theorem gap_le_product {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLpos : 0 < L) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (x (k + 1)) xbar →
      f (x (k + 1)) - f xbar ≤
        (Lf + Lbar + β * Lbar) * ‖x (k + 1) - x k‖ * ‖x (k + 1) - xbar‖ := by sorry

end NecoaraNG.FDM
