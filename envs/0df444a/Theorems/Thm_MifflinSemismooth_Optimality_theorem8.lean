-- Prove2me | Theorems.Thm_MifflinSemismooth_Optimality_theorem8
-- name    : MifflinSemismooth.Optimality.theorem8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:08.49198+00:00
-- url     : https://prove2.me/theorems/675aa335-3944-4413-9111-99d54edec1ee
-- title:
--   Theorem 8, p. 19 — semiconvex F on a convex X: F(x+d) ≦ F(x) implies F'(x;d) ≦ 0
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex and let $F:\mathbb R^n\to\mathbb R$ be semiconvex on $X$ (at each point of $X$, with respect to $X$). Let $x\in X$ and $d\in\mathbb R^n$ with $x+d\in X$. Then the directional derivative $F'(x;d)$ exists, and
--   $$
--   F(x+d)\le F(x)\quad\Longrightarrow\quad F'(x;d)\le 0.
--   $$
--
--   This is a nonsmooth analogue of the fact that a pseudoconvex function cannot increase infinitesimally in a direction along which it does not increase overall. In the proof of Theorem 9 it is applied to the constraint function $h$ at a point with $h(\bar x)=0$.
--
--   **Formalization Note** $F'(x;d)$ is the relation `HasDirDeriv`; the conclusion states that the limit exists and that every value it has is $\le 0$. Existence is part of Definition 2(b) at $x$, so the conjunct adds nothing beyond the page.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 19, Theorem 8

import Mathlib
import Definitions.Def_MifflinSemismooth_Optimality_Setting

namespace MifflinSemismooth.Optimality

/-- Mifflin (1976), §5, Theorem 8, p. 19: if `F` is semiconvex on a convex set `X`, `x ∈ X` and
`x + d ∈ X`, then `F(x + d) ≤ F(x)` implies `F'(x; d) ≤ 0`. -/
theorem theorem8 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : Convex ℝ X) (hF : MifflinSemismooth.Extremal.SemiconvexOn X F) (x d : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X)
    (hxd : x + d ∈ X) (hle : F (x + d) ≤ F x) :
    (∃ L, MifflinSemismooth.Extremal.HasDirDeriv F x d L) ∧ ∀ L, MifflinSemismooth.Extremal.HasDirDeriv F x d L → L ≤ 0 := by sorry

end MifflinSemismooth.Optimality
