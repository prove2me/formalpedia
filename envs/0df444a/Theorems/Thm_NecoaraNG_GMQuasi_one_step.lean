-- Prove2me | Theorems.Thm_NecoaraNG_GMQuasi_one_step
-- name    : NecoaraNG.GMQuasi.one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:40:55.216506+00:00
-- url     : https://prove2.me/theorems/94278c9b-3f01-4e38-bdd0-72d488bfe570
-- title:
--   Proof of Theorem 11, p. 20 — ‖x^{k+1} − x̄^k‖² ≤ (1 − α_kκ_f)‖x^k − x̄^k‖² − 2α_k(f(x^{k+1}) − f*)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be a nonempty closed convex set and let $f$ be a convex function on $X$, differentiable at every point of $X$, whose gradient is Lipschitz continuous on $X$ with constant $L_f>0$:
--   $$\|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|\qquad\forall x,y\in X.$$
--   Let $X^*=\arg\min_{x\in X}f(x)$ be nonempty, with optimal value $f^*$, and let $f$ be quasi-strongly convex with constant $\kappa_f>0$: for every $x\in X$ and $\bar x=[x]_{X^*}$ (the Euclidean projection of $x$ onto $X^*$),
--   $$f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa_f}{2}\|x-\bar x\|^2 .$$
--   That is, $f$ belongs to the class $q\mathcal S_{L_f,\kappa_f}(X)$.
--
--   Let $0<\alpha_k\le 1/L_f$, $x^k\in X$, $x^{k+1}=[x^k-\alpha_k\nabla f(x^k)]_X$ and $\bar x^k=[x^k]_{X^*}$. Then
--   $$\|x^{k+1}-\bar x^k\|^2\ \le\ (1-\alpha_k\kappa_f)\|x^k-\bar x^k\|^2-2\alpha_k\big(f(x^{k+1})-f^*\big).$$
--
--   This is the main inequality of the proof of Theorem 11; it is also iterated in the derivation of (50).
--
--   **Formalization Note** The standing assumptions of problem (P) are binders: $X$ closed and convex, $f$ convex on $X$ (`ConvexOn`), differentiable at each point of $X$ in the ambient space, the Lipschitz bound (1) with $L_f>0$, and a named minimiser `xstar` $\in X^*$ (so $X^*\neq\emptyset$; $f^*=f(\bar x)$ for any $\bar x\in X^*$). "Simple" (cheap projection) is not a mathematical hypothesis and is dropped; "closed convex function" adds nothing for a real-valued differentiable $f$. Projections $[u]_S$ are encoded by the nearest-point predicate `IsNearest S u p` ($p\in S$ and $\|u-p\|\le\|u-z\|$ for all $z\in S$), and statements hold for every nearest point; the nearest point onto a nonempty closed convex set is unique, so this is the projection. No hypothesis $\kappa_f\le L_f$ is added: the paper derives $\mu_f\le 1$ in (12) whenever $X\neq X^*$. Here $f^*$ is written $f(\bar x^k)$, which is exact since $\bar x^k\in X^*$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 20, proof of Theorem 11, display after "Further, we have"

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

open scoped InnerProductSpace

namespace NecoaraNG.GMQuasi

/-- One-step inequality, proof of Theorem 11, p. 20: for `0 < α ≤ 1/L_f`, with
`x̄^k = [x^k]_{X*}` and `f* = f(x̄^k)`,
`‖x^{k+1} - x̄^k‖² ≤ (1 - ακ)‖x^k - x̄^k‖² - 2α(f(x^{k+1}) - f*)`. -/
theorem one_step {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : NecoaraNG.Chain.QuasiStrong X f κ)
    (α : ℝ) (hα : 0 < α) (hαL : α ≤ 1 / Lf) :
    ∀ xk ∈ X, ∀ xk1, NecoaraNG.Chain.IsNearest X (xk - α • gradient f xk) xk1 →
      ∀ xkbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xk xkbar →
        ‖xk1 - xkbar‖ ^ 2 ≤ (1 - α * κ) * ‖xk - xkbar‖ ^ 2 - 2 * α * (f xk1 - f xkbar) := by sorry

end NecoaraNG.GMQuasi
