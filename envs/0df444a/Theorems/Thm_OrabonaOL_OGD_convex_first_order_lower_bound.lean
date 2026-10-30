-- Prove2me | Theorems.Thm_OrabonaOL_OGD_convex_first_order_lower_bound
-- name    : OrabonaOL.OGD.convex_first_order_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:37.232785+00:00
-- url     : https://prove2.me/theorems/e3017c73-c8ed-40f6-bd16-1212709e7f4d
-- title:
--   Theorem 2.7 — first-order lower bound for a convex function differentiable at a point
-- statement:
--   Let $S \subseteq \mathbb{R}^d$ and let $f : \mathbb{R}^d \to \mathbb{R}$ be convex on $S$ (in particular $S$ is convex). Let $x \in S$ and assume $f$ is differentiable at $x$, with gradient $\nabla f(x)$. Then
--
--   $$
--   f(y) \ge f(x) + \langle \nabla f(x), y - x \rangle \qquad \text{for all } y \in S .
--   $$
--
--   This is the book's Theorem 2.7, with the extended-valued convex function $f : \mathbb{R}^d \to (-\infty, +\infty]$ represented by its real values on its effective domain $S = \operatorname{dom} f$. It provides the linear lower bound on a convex function that drives the analysis of Online Gradient Descent (it is used in Theorem 2.8 and Lemma 2.12).
--
--   **Formalization Note** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`, $\nabla f(x)$ is Mathlib's `gradient f x`, and the inner product is `inner ℝ`.
--
--   Differences from the source:
--   - encoding: f : R^d → (−∞, +∞] convex; inequality for all y ∈ R^d → f : R^d → ℝ convex on S (S = dom f); inequality for y ∈ S; reason: for y ∉ dom f the book's inequality reads +∞ ≥ … and has no content; on dom f the two functions agree
--   - generalization: x ∈ int dom f → x ∈ S; reason: differentiability at x already concerns a whole neighbourhood of x and the inequality only uses the segment [x, y] ⊆ S; taking x ∈ int S recovers the book's statement
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 11 (PDF p. 23), Theorem 2.7 (Rockafellar 1970, Theorem 25.1 and Corollary 25.1.1)

import Mathlib

namespace OrabonaOL.OGD

/-- **Theorem 2.7 (first-order lower bound for a differentiable convex function).**
Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 11 (PDF p. 23),
Theorem 2.7 (Rockafellar, 1970, Theorem 25.1 and Corollary 25.1.1).

Let `f` be convex on a convex set `S` (the book's `dom f`), `x ∈ S`, and `f` differentiable
at `x`. Then `f y ≥ f x + ⟪∇f(x), y − x⟫` for every `y ∈ S`.

**Formalization Note.** The book's extended-valued `f : ℝ^d → (−∞, +∞]` is encoded as a real
function `f` together with its effective domain `S`; for `y ∉ S` the book's inequality reads
`+∞ ≥ …` and has no content. The book assumes `x ∈ int dom f`; here `x ∈ S` suffices, which
specializes to the book's statement. -/
theorem convex_first_order_lower_bound {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ S f)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ S) (hdiff : DifferentiableAt ℝ f x) :
    ∀ y ∈ S, f x + inner ℝ (gradient f x) (y - x) ≤ f y := by sorry

end OrabonaOL.OGD
