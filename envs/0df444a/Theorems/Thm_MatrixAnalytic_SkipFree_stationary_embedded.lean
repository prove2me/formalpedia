-- Prove2me | Theorems.Thm_MatrixAnalytic_SkipFree_stationary_embedded
-- name    : MatrixAnalytic.SkipFree.stationary_embedded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:45.296555+00:00
-- url     : https://prove2.me/theorems/fa3582c5-d235-4ec4-afa8-35d097e9e2c7
-- title:
--   Corollary 13.1.2 — the stationary vector of an M/G/1-type chain is proportional to the sublevel-0 part of that of its QBD
-- statement:
--   Let $\tilde P$ be the transition matrix (13.1) of an irreducible, positive recurrent M/G/1-type Markov chain with stationary probability vector $\tilde\pi=(\tilde\pi_0,\tilde\pi_1,\dots)$, partitioned by levels. Let $\pi=(\pi_{00},\pi_{01},\pi_{02},\dots,\pi_{10},\pi_{11},\pi_{12},\dots)$ be a stationary probability vector of the three-dimensional process $\{(X_t,D_t,J_t)\}$ with transition matrix (13.3), blocks (13.4)–(13.7), partitioned by sublevels: $\pi_{n,d}$ is the row vector of the states $(n,d,j)$. Then there is a constant $c$ such that
--   $$\tilde\pi_i=c\,\pi_{i,0}\qquad\text{for }i\ge0.$$
--
--   The corollary reduces the stationary distribution of the M/G/1-type chain to that of a QBD, to which the methods of the earlier chapters apply.
--
--   **Formalization Note** The book's "the stationary probability vector of (13.1)" is rendered as hypotheses: (13.1) is stochastic, irreducible and positive recurrent (return-time notion), and $\tilde\pi$ is a stationary probability vector of it; $\pi$ is any stationary probability vector of (13.3). The constant $c$ is existentially quantified, as the book's "normalizing constant".
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 271, Corollary 13.1.2

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal

namespace MatrixAnalytic.SkipFree

/-- Corollary 13.1.2 (p. 271). Let `π̃` be the stationary probability vector of an irreducible,
positive recurrent M/G/1-type chain (13.1), and `π = (π₀₀, π₀₁, …, π₁₀, π₁₁, …)` a stationary
probability vector of the three-dimensional process `{(X_t, D_t, J_t)}` with transition matrix
(13.3), indexed by level `n` and phase `(d, j)`. Then `π̃_n = c π_{n,0}` for all `n ≥ 0`, for a
constant `c`. -/
theorem stationary_embedded {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ) (π : ℕ × (ℕ × ι) → ℝ)
    (hP : IsStochasticC (mg1P D C))
    (hirr : IrreducibleC (mg1P D C))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (mg1P D C) x)
    (hπt : IsStationaryC (mg1P D C) πt)
    (hπ : IsStationaryC (mg1QBD D C) π) :
    ∃ c : ℝ, ∀ (n : ℕ) (j : ι), πt (n, j) = c * π (n, (0, j)) := by sorry

end MatrixAnalytic.SkipFree
