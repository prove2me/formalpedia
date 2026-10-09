-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_eq_3_13c
-- name    : IQCAlg.ConvexIQC.eq_3_13c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:34.388747+00:00
-- url     : https://prove2.me/theorems/0d1187be-4964-48e6-8b78-002bf5f307f9
-- title:
--   (3.13c), Proposition 5, p. 13 — co-coercivity: f(y) ≥ f(x) + ∇f(x)ᵀ(y − x) + ‖∇f(y) − ∇f(x)‖²/(2L)
-- statement:
--   Let $L>0$ and let $f:\mathbb R^d\to\mathbb R$ be convex and continuously differentiable with $L$-Lipschitz gradient, $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$. Then for all $x,y\in\mathbb R^d$,
--   $$f(y)\ \ge\ f(x)+\nabla f(x)^{\mathsf T}(y-x)+\frac1{2L}\,\|\nabla f(y)-\nabla f(x)\|^2 .$$
--
--   This is property (3.13c) of Proposition 5, one of the two co-coercivity inequalities. The proof of Lemma 8 applies it to the auxiliary function $g(x)=f(x)-f(y_\star)-\tfrac m2\|x-y_\star\|^2$, which is convex with $(L-m)$-Lipschitz gradient.
--
--   **Formalization Note** Proposition 5 states (3.13c) for $f\in S(m,L)$; it is stated here for convex $f$ with $L$-Lipschitz gradient (the case $m=0$, written $g\in S(0,L-m)$ in the proof of Lemma 8), which contains the page's statement and is the form the proof of Lemma 8 uses.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 13, Proposition 5, (3.13c)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- (3.13c), Proposition 5, p. 13, in the convex case `m = 0` used by the proof of Lemma 8. -/
theorem eq_3_13c {d : ℕ} (f : E d → ℝ) (L : ℝ) (hL : 0 < L) (hdiff : ContDiff ℝ 1 f)
    (hconv : ConvexOn ℝ Set.univ f)
    (hlip : ∀ x y : E d, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    ∀ x y : E d,
      f x + ⟪gradient f x, y - x⟫_ℝ + 1 / (2 * L) * ‖gradient f y - gradient f x‖ ^ 2 ≤ f y := by sorry

end IQCAlg.ConvexIQC
