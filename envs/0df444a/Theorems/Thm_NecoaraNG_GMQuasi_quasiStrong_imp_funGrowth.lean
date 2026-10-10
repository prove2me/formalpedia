-- Prove2me | Theorems.Thm_NecoaraNG_GMQuasi_quasiStrong_imp_funGrowth
-- name    : NecoaraNG.GMQuasi.quasiStrong_imp_funGrowth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:14.676993+00:00
-- url     : https://prove2.me/theorems/2b71ef29-3c0d-46ce-831c-2a690b13db47
-- title:
--   Proof of Theorem 11, p. 20 (Theorem 4) — quasi-strong convexity (10) implies quadratic functional growth (22) with the same κ_f
-- statement:
--   Let $X\subseteq\mathbb R^n$ be a nonempty closed convex set and let $f$ be a convex function on $X$, differentiable at every point of $X$, whose gradient is Lipschitz continuous on $X$ with constant $L_f>0$:
--   $$\|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|\qquad\forall x,y\in X.$$
--   Let $X^*=\arg\min_{x\in X}f(x)$ be nonempty, with optimal value $f^*$, and let $f$ be quasi-strongly convex with constant $\kappa_f>0$: for every $x\in X$ and $\bar x=[x]_{X^*}$ (the Euclidean projection of $x$ onto $X^*$),
--   $$f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa_f}{2}\|x-\bar x\|^2 .$$
--   That is, $f$ belongs to the class $q\mathcal S_{L_f,\kappa_f}(X)$.
--
--   Then $f$ has quadratic functional growth with the same constant: for every $x\in X$ and $\bar x=[x]_{X^*}$,
--   $$f(x)-f^*\ \ge\ \frac{\kappa_f}{2}\|x-\bar x\|^2 .$$
--
--   In the proof of Theorem 11 this is applied at $x^{k+1}$, through the chain of Theorem 4, $(10)\Rightarrow(17)\Rightarrow(13)\Rightarrow(22)$.
--
--   **Formalization Note** The standing assumptions of problem (P) are binders: $X$ closed and convex, $f$ convex on $X$ (`ConvexOn`), differentiable at each point of $X$ in the ambient space, the Lipschitz bound (1) with $L_f>0$, and a named minimiser `xstar` $\in X^*$ (so $X^*\neq\emptyset$; $f^*=f(\bar x)$ for any $\bar x\in X^*$). "Simple" (cheap projection) is not a mathematical hypothesis and is dropped; "closed convex function" adds nothing for a real-valued differentiable $f$. Projections $[u]_S$ are encoded by the nearest-point predicate `IsNearest S u p` ($p\in S$ and $\|u-p\|\le\|u-z\|$ for all $z\in S$), and statements hold for every nearest point; the nearest point onto a nonempty closed convex set is unique, so this is the projection. No hypothesis $\kappa_f\le L_f$ is added: the paper derives $\mu_f\le 1$ in (12) whenever $X\neq X^*$. The statement is the composition of Theorem 1 ($(10)\Rightarrow(13)$) and the last link of Theorem 4 ($(13)\Rightarrow(22)$); it is posed again here because draft items cannot import another mission's drafts.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 20, proof of Theorem 11 (citing Theorem 4, p. 9)

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

open scoped InnerProductSpace

namespace NecoaraNG.GMQuasi

/-- Proof of Theorem 11, p. 20 (via Theorem 4, p. 9): for a convex `f` with
`L_f`-Lipschitz gradient on `X`, quasi-strong convexity (10) with constant `κ` implies quadratic
functional growth (22) with the same constant `κ`. -/
theorem quasiStrong_imp_funGrowth {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : NecoaraNG.Chain.QuasiStrong X f κ) :
    NecoaraNG.Chain.QuadFunGrowth X f κ := by sorry

end NecoaraNG.GMQuasi
