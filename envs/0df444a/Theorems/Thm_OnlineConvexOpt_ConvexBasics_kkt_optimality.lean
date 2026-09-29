-- Prove2me | Theorems.Thm_OnlineConvexOpt_ConvexBasics_kkt_optimality
-- name    : OnlineConvexOpt.ConvexBasics.kkt_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T18:33:50.103062+00:00
-- url     : https://prove2.me/theorems/f573edf5-1f5d-4915-920d-7af47dd44cb4
-- title:
--   Theorem 2.2 — Karush-Kuhn-Tucker optimality condition
-- statement:
--   **Statement (Theorem 2.2).** Let $K \subseteq E$ be a convex set in a real inner product space and let $x^\star \in \arg\min_{x \in K} f(x)$. Then for every $y \in K$,
--   $$\langle \nabla f(x^\star),\, y - x^\star \rangle \ge 0.$$
--
--   This is the multi-dimensional first-order optimality condition for constrained convex minimization: at an optimum, the negative gradient cannot point into the feasible set $K$, since moving in the direction $y - x^\star$ for any feasible $y$ can only be a non-decreasing direction for $f$. It generalizes the unconstrained fact $\nabla f(x) = 0 \iff x \in \arg\min f$ (the case $K = E$, where $y - x^\star$ ranges over all of $E$ so the inequality forces $\nabla f(x^\star) = 0$), and underlies the KKT theory the book refers to for general constrained programs.
--
--   **Formalization Note.** $f$ need not be convex or differentiable everywhere; only that $f$ attains its minimum over $K$ at $x^\star$ (via `IsMinOn`) and that $f$ has a gradient at the single point $x^\star$ (via `HasGradientAt`) is assumed, matching exactly what the book's proof (an elementary first-order argument along the segment towards $y$) uses.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 21, Theorem 2.2 (PDF p. 43)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ConvexBasics

/-- Theorem 2.2 (Karush-Kuhn-Tucker; Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 21, PDF p. 43). Let `K ⊆ R^d` be a convex set and
`x⋆ ∈ arg min_{x ∈ K} f(x)`. Then for any `y ∈ K`, `⟪∇f(x⋆), y - x⋆⟫_ℝ ≥ 0`. -/
theorem kkt_optimality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K : Set E) (hK : Convex ℝ K) (f : E → ℝ)
    (xstar : E) (hxstarK : xstar ∈ K) (hxstar : IsMinOn f K xstar)
    (gstar : E) (hgstar : HasGradientAt f gstar xstar) :
    ∀ y ∈ K, ⟪gstar, y - xstar⟫_ℝ ≥ 0 := by sorry

end OnlineConvexOpt.ConvexBasics
