-- Prove2me | Theorems.Thm_GeometryOfGraphs_EuclidDist_gram_reformulation
-- name    : GeometryOfGraphs.EuclidDist.gram_reformulation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:15.966316+00:00
-- url     : https://prove2.me/theorems/5c70f1b0-cbb0-4826-a371-2429f28c313c
-- title:
--   Proof of Corollary 3.5, first display — distortion ≤ c iff a PSD A has d²ᵢⱼ ≤ aᵢᵢ + aⱼⱼ − 2aᵢⱼ ≤ c²d²ᵢⱼ
-- statement:
--   Let $(X,d)$ be a finite semi-metric space, with points indexed by $X$, and let $c \ge 1$. Then $(X,d)$ embeds in a Euclidean space with distortion at most $c$ if and only if there is a real positive semidefinite matrix $A = (a_{i,j})_{i,j \in X}$ such that
--
--   $$
--   d_{i,j}^2 \;\le\; a_{i,i} + a_{j,j} - 2a_{i,j} \;\le\; c^2 d_{i,j}^2 \qquad \text{for all } i, j \in X .
--   $$
--
--   Here $d_{i,j} = d(i,j)$. The quantity $a_{i,i}+a_{j,j}-2a_{i,j}$ is the squared distance between the $i$-th and $j$-th points when $A$ is the Gram matrix of a point configuration. The statement is the first display of the proof of Corollary 3.5 (p. 224), which recalls the observation made in the proof of Theorem 3.2, Claim 2 (p. 221): there $A = MM^t$ for the matrix $M$ whose rows are the images of a distortion-$c$ embedding, and $\frac{1}{c^2}d_{i,j}^2 \le a_{i,i}+a_{j,j}-2a_{i,j} \le d_{i,j}^2$; the two forms differ by the scaling $A \mapsto c^2 A$.
--
--   The reformulation turns the existence of an embedding into the feasibility of a semidefinite system, linear in $A$, which is what the duality argument of Corollary 3.5 analyses.
--
--   **Formalization Note** $A$ is a `Matrix X X ℝ` with `Matrix.PosSemidef` (which includes symmetry). The inequalities are required for all ordered pairs $(i,j)$, including $i=j$, where they read $0 \le 0 \le 0$. The distortion notion is the contractive one of the definition `EuclideanDistortion`.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 224, proof of Corollary 3.5, first display; cf. p. 221, proof of Theorem 3.2, Claim 2

import Mathlib
import Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion

namespace GeometryOfGraphs.EuclidDist

/-- Proof of Corollary 3.5, first display (p. 224), cf. proof of Theorem 3.2, Claim 2 (p. 221):
a finite metric space embeds in Euclidean space with distortion at most `c` iff some positive
semidefinite matrix `A` satisfies `d i j ^ 2 ≤ a_ii + a_jj - 2 a_ij ≤ c ^ 2 * d i j ^ 2`. -/
theorem gram_reformulation {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    EmbedsEuclidean d c ↔
      ∃ A : Matrix X X ℝ, A.PosSemidef ∧
        ∀ i j, d i j ^ 2 ≤ A i i + A j j - 2 * A i j ∧
          A i i + A j j - 2 * A i j ≤ c ^ 2 * d i j ^ 2 := by sorry

end GeometryOfGraphs.EuclidDist
