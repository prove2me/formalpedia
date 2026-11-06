-- Prove2me | Theorems.Thm_IntervalToDynamic_lemma_13
-- name    : IntervalToDynamic.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:14.535023+00:00
-- url     : https://prove2.me/theorems/5404fc16-54d7-462d-a42e-1758e1f50954
-- title:
--   Lemma 13 — projection correction: $\|d\|\le\|g\|$ and $g^\top(x-u)\le d^\top(y-u)$
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$ be closed and convex, and let $g\in\mathbb R^d$ satisfy $\|g\|_2\le G$ for some $G\ge0$. For every $u\in\mathcal X$ and every $y\in\mathbb R^d$, put $x=\Pi_{\mathcal X}[y]$, $n=y-x$, and let $\mathsf d$ be the corrected gradient of $g$ at $n$, so that $\mathsf d=g+\frac{\max\{-g^\top n,0\}}{\|n\|_2^2}n$, with $\mathsf d=g$ when $n=0$. Then
--   $$
--   \|\mathsf d\|_2\le\|g\|_2\le G,\qquad g^\top(x-u)\le \mathsf d^\top(y-u).
--   $$
--
--   The lemma lets a linearized loss at the projected point $x$ be charged to the unprojected decision $y$ without growing the gradient, which is the basis of domain conversion.
--
--   Differences from the source: none.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 13, p.30

import Mathlib
import Definitions.Def_IntervalToDynamic_proj
import Definitions.Def_IntervalToDynamic_correctedGrad

namespace IntervalToDynamic

/-- Lemma 13 (projection correction). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 13, p.30.

Let `X ⊆ ℝ^d` be closed and convex and `‖g‖₂ ≤ G`, `G ≥ 0`. For every `u ∈ X` and every `y ∈ ℝ^d`,
with `x = Π_X[y]`, `n = y − x` and `d = correctedGrad g n`, one has `‖d‖₂ ≤ ‖g‖₂ ≤ G` and
`gᵀ(x − u) ≤ dᵀ(y − u)`.

**Formalization Note.** `X` is nonempty because `u ∈ X`, so `proj X y` is the projection. -/
theorem lemma_13 {d : ℕ} (hd : 0 < d) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXv : Convex ℝ X)
    (g : EuclideanSpace ℝ (Fin d)) (G : ℝ) (hG : 0 ≤ G) (hg : ‖g‖ ≤ G) (u y : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X) :
    ‖correctedGrad g (y - proj X y)‖ ≤ ‖g‖ ∧ ‖g‖ ≤ G ∧
      inner ℝ g (proj X y - u) ≤ inner ℝ (correctedGrad g (y - proj X y)) (y - u) := by sorry

end IntervalToDynamic
