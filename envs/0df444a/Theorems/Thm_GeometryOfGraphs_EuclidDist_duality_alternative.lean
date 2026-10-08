-- Prove2me | Theorems.Thm_GeometryOfGraphs_EuclidDist_duality_alternative
-- name    : GeometryOfGraphs.EuclidDist.duality_alternative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:10.69048+00:00
-- url     : https://prove2.me/theorems/b96adfeb-5630-4a90-9272-76c2b5ec9349
-- title:
--   Proof of Corollary 3.5, duality step — no PSD A satisfies all J_{i,j} iff a PSD Q and a nonnegative combination of the J_{i,j} give a contradiction
-- statement:
--   Let $(X,d)$ be a finite semi-metric space and $c \ge 1$. For $i,j \in X$ consider the pair of inequalities in the unknown matrix $A=(a_{i,j})$
--
--   $$
--   J_{i,j}:\qquad c^2 d_{i,j}^2 \;\ge\; a_{i,i}+a_{j,j}-2a_{i,j} \;\ge\; d_{i,j}^2 .
--   $$
--
--   Then **no** real positive semidefinite matrix $A$ satisfies every $J_{i,j}$ if and only if there exist a real positive semidefinite matrix $Q=(q_{i,j})$ and nonnegative multipliers $\lambda_{i,j}, \mu_{i,j} \ge 0$ such that, for **every** matrix $A$,
--
--   $$
--   \sum_{i,j} q_{i,j}\,a_{i,j} \;+\; \sum_{i,j}\Big(\lambda_{i,j}\big(c^2d_{i,j}^2-(a_{i,i}+a_{j,j}-2a_{i,j})\big) + \mu_{i,j}\big((a_{i,i}+a_{j,j}-2a_{i,j})-d_{i,j}^2\big)\Big) \;=\; \sum_{i,j}\big(\lambda_{i,j}c^2d_{i,j}^2-\mu_{i,j}d_{i,j}^2\big),
--   $$
--
--   and the constant on the right is negative:
--
--   $$
--   \sum_{i,j}\big(\lambda_{i,j}c^2d_{i,j}^2-\mu_{i,j}d_{i,j}^2\big) \;<\; 0 .
--   $$
--
--   This is the theorem of alternatives invoked on pp. 224–225 in the proof of Corollary 3.5: "the conclusion of the Corollary is incorrect, i.e., no such matrix $A$ exists, iff there is a matrix $Q\in PSD$ such that the inequality $\sum_{i,j} a_{i,j}q_{i,j}\ge 0$ contradicts some nonnegative combination of the inequalities $J_{i,j}$." The identity says that adding $\sum_{i,j}q_{i,j}a_{i,j} \ge 0$ to $\lambda_{i,j}$ times the left part and $\mu_{i,j}$ times the right part of each $J_{i,j}$ eliminates every $a$-term, and the negative constant is the contradiction $0 \le (\text{negative number})$.
--
--   **Formalization Note** "Contradicts some nonnegative combination" is made precise as the exact cancellation identity above (holding for all matrices $A$, an identity of linear forms) together with a negative constant term; $\lambda$ and $\mu$ are written `lam` and `mu`. Pairs $(i,j)$ are ordered and include $i=j$. The number $1$ multiplying $\sum q_{i,j}a_{i,j}$ loses no generality, since $Q$ can be rescaled.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), pp. 224–225, proof of Corollary 3.5 (paragraph after Proposition 3.6, inequalities J_{i,j})

import Mathlib
import Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion

namespace GeometryOfGraphs.EuclidDist

/-- Proof of Corollary 3.5, duality step (pp. 224–225): no positive semidefinite `A` satisfies the
inequalities `J_ij : c^2 d_ij^2 ≥ a_ii + a_jj - 2 a_ij ≥ d_ij^2` iff there are a positive
semidefinite `Q` and nonnegative multipliers `lam, mu` such that adding
`∑ a_ij q_ij ≥ 0` to the combination `∑ lam_ij (upper J_ij) + mu_ij (lower J_ij)` cancels every
`a`-term and leaves a negative constant on the right, i.e. a contradiction. -/
theorem duality_alternative {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    (¬ ∃ A : Matrix X X ℝ, A.PosSemidef ∧
        ∀ i j, d i j ^ 2 ≤ A i i + A j j - 2 * A i j ∧
          A i i + A j j - 2 * A i j ≤ c ^ 2 * d i j ^ 2) ↔
      ∃ Q : Matrix X X ℝ, Q.PosSemidef ∧
        ∃ lam mu : X → X → ℝ, (∀ i j, 0 ≤ lam i j) ∧ (∀ i j, 0 ≤ mu i j) ∧
          (∀ A : Matrix X X ℝ,
            (∑ i, ∑ j, Q i j * A i j) +
              ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2 - (A i i + A j j - 2 * A i j)) +
                mu i j * ((A i i + A j j - 2 * A i j) - d i j ^ 2)) =
            ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2)) ∧
          ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2) < 0 := by sorry

end GeometryOfGraphs.EuclidDist
