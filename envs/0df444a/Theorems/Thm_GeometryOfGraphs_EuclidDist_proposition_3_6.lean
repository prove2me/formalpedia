-- Prove2me | Theorems.Thm_GeometryOfGraphs_EuclidDist_proposition_3_6
-- name    : GeometryOfGraphs.EuclidDist.proposition_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:03.822986+00:00
-- url     : https://prove2.me/theorems/85d9e5d0-c84a-4eeb-b857-519c437c6a8f
-- title:
--   Proposition 3.6 — a symmetric P is PSD iff Σᵢⱼ pᵢⱼ yᵢⱼ ≥ 0 for every PSD Y
-- statement:
--   Let $X$ be a finite index set and let $P = (p_{i,j})_{i,j\in X}$ be a real symmetric matrix. Then $P$ is positive semidefinite if and only if
--
--   $$
--   \sum_{i,j} p_{i,j}\, y_{i,j} \;\ge\; 0 \qquad \text{for every real positive semidefinite matrix } Y = (y_{i,j}).
--   $$
--
--   In other words, the cone $PSD_n$ of real symmetric positive semidefinite $n\times n$ matrices is self-dual under the trace pairing $\langle P, Y\rangle = \sum_{i,j} p_{i,j} y_{i,j}$. The paper uses it as the complete list of linear inequalities defining $PSD_n$, which is what the duality step in the proof of Corollary 3.5 needs.
--
--   **Formalization Note** The page says "a matrix $P$ belongs to $PSD_n$", and $PSD_n$ is defined on the same page as a cone of *symmetric* matrices. The hypothesis that $P$ is symmetric (`P.IsSymm`) is therefore made explicit: without it the "if" direction would be false, since a nonzero antisymmetric $P$ pairs to $0$ with every symmetric $Y$. Matrices are indexed by an arbitrary finite type rather than $\{1,\dots,n\}$.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 224, Proposition 3.6

import Mathlib

namespace GeometryOfGraphs.EuclidDist

/-- Proposition 3.6 (p. 224): a real symmetric matrix `P` is positive semidefinite iff
`∑_{i,j} p_ij * y_ij ≥ 0` for every positive semidefinite `Y`. -/
theorem proposition_3_6 {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P.IsSymm) :
    P.PosSemidef ↔
      ∀ Y : Matrix X X ℝ, Y.PosSemidef → 0 ≤ ∑ i, ∑ j, P i j * Y i j := by sorry

end GeometryOfGraphs.EuclidDist
