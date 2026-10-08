-- Prove2me | Theorems.Thm_MatousekLP_Simplex_cycle_same_bfs
-- name    : MatousekLP.Simplex.cycle_same_bfs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:03:32.976265+00:00
-- url     : https://prove2.me/theorems/2da63b48-e767-4606-beb8-2d7c77a26aa0
-- title:
--   Claim in the proof of Theorem 5.8.1 — a cycle of the simplex method stays at one basic feasible solution
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ with $n\ge m$, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$. Suppose the simplex method, with any pivot rule, cycles: there are bases
--   $$B_0\to B_1\to\dots\to B_k=B_0,\qquad k\ge1,$$
--   where each $B_{t+1}$ arises from the feasible basis $B_t$ by a pivot step (an entering variable with positive coefficient in the last row of $T(B_t)$ and a leaving variable satisfying the ratio rule (5.3)). Call a variable **fickle** if it enters the basis at some step of the cycle. Then there is a single feasible solution $x$ that is the basic feasible solution of every $B_t$, $0\le t\le k$, and $x_j=0$ for every fickle variable $x_j$.
--
--   This is the first step of the proof that Bland's rule prevents cycling: it reduces a cycle to a sequence of degenerate pivots at one vertex.
--
--   **Formalization Note** Indices are 0-based. The cycle is a function $t\mapsto B_t$ on $\{0,\dots,k\}$; a fickle variable is an index $j\in B_{t+1}\setminus B_t$ for some $t<k$. The standing assumption of §4.2 is a hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 73, Claim in the proof of Theorem 5.8.1

import Mathlib
import Definitions.Def_MatousekLP_Simplex_Tableau
open Matrix Filter

namespace MatousekLP.Simplex

/-- Claim in the proof of Theorem 5.8.1 (p. 73), valid for any pivot rule. Suppose the simplex
method cycles: `B₀, B₁, …, B_k = B₀` (`k ≥ 1`) with each `B_{t+1}` obtained from `B_t` by a pivot
step. Then all bases of the cycle yield the same basic feasible solution `x`, and every fickle
variable (one that enters the basis at some step of the cycle) is `0` in `x`.
Standing assumption of §4.2 (p. 44): `n ≥ m` and `A` has rank `m`. -/
theorem cycle_same_bfs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (k : ℕ) (hk : 1 ≤ k)
    (Bs : ℕ → Finset (Fin n)) (hstep : ∀ t, t < k → SimplexStep A b c (Bs t) (Bs (t + 1)))
    (hcycle : Bs k = Bs 0) :
    ∃ x : Fin n → ℝ, MatousekLP.BFS.IsFeasible A b x ∧
      (∀ t, t ≤ k → IsBasicSolutionFor A b (Bs t) x) ∧
      ∀ t, t < k → ∀ j, j ∈ Bs (t + 1) → j ∉ Bs t → x j = 0 := by sorry

end MatousekLP.Simplex
