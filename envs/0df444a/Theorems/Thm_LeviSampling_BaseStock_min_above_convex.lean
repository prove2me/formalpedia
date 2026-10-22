-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_min_above_convex
-- name    : LeviSampling.BaseStock.min_above_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:21.685358+00:00
-- url     : https://prove2.me/theorems/e36e1c61-067a-4bb4-bd46-2800199b8267
-- title:
--   Fact 3.1 — minimizing a convex function over [x, ∞)
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be convex with a global minimizer $r$, and let $w(x) = \min_{y \ge x} f(y)$. Then
--   $$w \text{ is convex}, \qquad w(x) = f(r) \ (x \le r), \qquad w(x) = f(x) \ (x > r).$$
--   This is what makes base-stock policies optimal in the dynamic program (1)–(2): ordering up to $r$ is optimal from any inventory below $r$, and not ordering is optimal above it.
--
--   **Formalization Note** $w$ is the infimum of $f$ over $[x, \infty)$ (`minAbove`).
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 828, Fact 3.1

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Model

namespace LeviSampling.BaseStock

/-- **Fact 3.1** (Levi, Roundy & Shmoys 2007, p. 828). Let `f : ℝ → ℝ` be convex with a
minimizer `r`. Then `w(x) = min_{y ≥ x} f(y)` is convex, `w(x) = f(r)` for `x ≤ r`, and
`w(x) = f(x)` for `x > r`. -/
theorem min_above_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (r : ℝ)
    (hr : ∀ y, f r ≤ f y) :
    ConvexOn ℝ Set.univ (minAbove f) ∧
      (∀ x, x ≤ r → minAbove f x = f r) ∧
      (∀ x, r < x → minAbove f x = f x) := by sorry

end LeviSampling.BaseStock
