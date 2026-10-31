-- Prove2me | Theorems.Thm_MultimodularDocks_fact_2
-- name    : MultimodularDocks.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:45.707991+00:00
-- url     : https://prove2.me/theorems/f714caa9-50f4-4d79-a0ae-88ccf8e1c02b
-- title:
--   Fact 2 — a non-minimizer of a separable convex function has an improving exchange (with box constraints)
-- statement:
--   Let $S$ be a finite index set and $f(\vec x)=\sum_i f_i(x_i)$, where each $f_i$ is convex on $\{0,1,\dots,\mathrm{cap}_i\}$. Let $\vec x$ satisfy $0\le x_i\le \mathrm{cap}_i$ and $\sum_i x_i=B$, and suppose $\vec x$ does not minimize $f$ under these constraints: some $\vec y$ with $0\le y_i\le\mathrm{cap}_i$ and $\sum_i y_i=B$ has $f(\vec y)<f(\vec x)$. Then there are indices $i\ne j$ with $x_i+1\le\mathrm{cap}_i$, $x_j\ge 1$ and
--
--   $$
--   f(\vec x+e_i-e_j)<f(\vec x).
--   $$
--
--   This is the marginal-value principle of separable convex resource allocation; it reduces the optimality of a bike placement to the absence of an improving single bike move.
--
--   Differences from the source:
--   - generalization: nonnegative integers x_i with Σ x_i = B, each f_i convex; conclusion: some i, j with f(x + e_i − e_j) < f(x) → box 0 ≤ x_i ≤ cap_i, f_i convex on {0, …, cap_i}; conclusion adds i ≠ j and x + e_i − e_j in the box; reason: with cap_i = B the box is implied by the constraints and the hypothesis by convexity, so it specializes to the printed fact; the box is what Lemma 3.1 needs, since Fact 1 gives convexity on {0, …, d + b} only
--   - encoding: 'x does not minimize f subject to Σ x_i = B'; 'f_i convex' → some feasible y has f(y) < f(x); nonnegative second differences on the box; reason: same statements on integer domains
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, App. C.1, Fact 2, p.44

import Mathlib

namespace MultimodularDocks

/-- **Fact 2** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, App. C.1, Fact 2, p.44), with
box constraints. Let `f(x⃗) = ∑_i f_i(x_i)` where each `f_i` is convex on `{0, 1, …, cap_i}`.
If `x⃗` with `0 ≤ x_i ≤ cap_i` and `∑_i x_i = B` does not minimize `f` subject to these
constraints (some `y⃗` with `0 ≤ y_i ≤ cap_i`, `∑_i y_i = B` has `f(y⃗) < f(x⃗)`), then there are
`i ≠ j` with `x⃗ + e_i − e_j` again in the box and `f(x⃗ + e_i − e_j) < f(x⃗)`.

**Formalization Note** The page has nonnegative integers and each `f_i` convex; the box
`x_i ≤ cap_i` is what Lemma 3.1 needs (Fact 1 gives convexity on `{0, …, d + b}` only). With
`cap_i = B` it is the printed statement. Convexity on `{0, …, cap_i}` is stated through second
differences. -/
theorem fact_2 {S : Type*} [Fintype S] [DecidableEq S] (f : S → ℤ → ℝ) (cap : S → ℤ)
    (hconv : ∀ i k, 1 ≤ k → k + 1 ≤ cap i → 2 * f i k ≤ f i (k - 1) + f i (k + 1))
    (B : ℤ) (x y : S → ℤ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ cap i) (hxB : ∑ i, x i = B)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ cap i) (hyB : ∑ i, y i = B)
    (hlt : ∑ i, f i (y i) < ∑ i, f i (x i)) :
    ∃ i j, i ≠ j ∧ x i + 1 ≤ cap i ∧ 1 ≤ x j ∧
      ∑ k, f k ((x + Pi.single i 1 - Pi.single j 1 : S → ℤ) k) < ∑ k, f k (x k) := by sorry

end MultimodularDocks
