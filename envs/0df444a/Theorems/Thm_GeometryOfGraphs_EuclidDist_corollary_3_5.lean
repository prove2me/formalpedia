-- Prove2me | Theorems.Thm_GeometryOfGraphs_EuclidDist_corollary_3_5
-- name    : GeometryOfGraphs.EuclidDist.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:08.146378+00:00
-- url     : https://prove2.me/theorems/381835f4-fbd3-47e5-962f-468dc47cf3b1
-- title:
--   Corollary 3.5 — distortion ≤ c into Euclidean space iff Σ_{q>0} q d² + c² Σ_{q<0} q d² ≤ 0 for every PSD Q with Q·1 = 0
-- statement:
--   Let $(X,d)$ be a finite semi-metric space ($n = |X|$ points, distances $d_{i,j} = d(i,j)$) and let $c \ge 1$. Then $(X,d)$ embeds in a Euclidean space with distortion at most $c$ if and only if for every real positive semidefinite matrix $Q = (q_{i,j})_{i,j\in X}$ with $Q\cdot\vec 1 = \vec 0$ (every row sums to zero)
--
--   $$
--   \sum_{q_{i,j}>0} q_{i,j}\, d_{i,j}^2 \;+\; c^2 \sum_{q_{i,j}<0} q_{i,j}\, d_{i,j}^2 \;\le\; 0 .
--   $$
--
--   The sums run over ordered pairs $(i,j)$ with $q_{i,j} > 0$, respectively $q_{i,j} < 0$, as printed; diagonal terms vanish because $d_{i,i}=0$.
--
--   The corollary characterises the least Euclidean distortion $c_2(X)$ of a finite metric space by a family of linear inequalities in the squared distances, indexed by the positive semidefinite matrices with zero row sums: each such $Q$ certifies a lower bound on $c_2(X)$, and the corollary says that these certificates are complete. For $c=1$ it reduces to the classical characterisation of finite metric spaces that embed isometrically in Euclidean space (Remark 3.7).
--
--   **Formalization Note** "May be embedded with distortion $\le c$" means that an embedding with distortion at most $c$ exists (attained), using the contractive form $\|\varphi(x)-\varphi(y)\| \le d(x,y) \le c\|\varphi(x)-\varphi(y)\|$ of Definition 2.1; the target $\mathbb{R}^m$ has an existentially quantified dimension. "Metric space" is a semi-metric as allowed by the paper (p. 218, footnote 1). The positive semidefinite cone is `Matrix.PosSemidef` (symmetric by definition) and $Q\cdot\vec1=\vec0$ is `Q.mulVec (fun _ => 1) = 0`. The corollary's second sentence ("In particular … with $c = O(\log n)$") rests on Bourgain's embedding theorem, which the paper only cites, and is not part of this statement.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 224, Corollary 3.5 (first sentence)

import Mathlib
import Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion

namespace GeometryOfGraphs.EuclidDist

/-- Corollary 3.5 (p. 224), first sentence: a finite metric space `(X, d)` embeds in a Euclidean
space with distortion at most `c` iff for every positive semidefinite `Q` with `Q · 1 = 0`,
`∑_{q_ij > 0} q_ij d_ij^2 + c^2 ∑_{q_ij < 0} q_ij d_ij^2 ≤ 0` (sums over ordered pairs). -/
theorem corollary_3_5 {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    EmbedsEuclidean d c ↔
      ∀ Q : Matrix X X ℝ, Q.PosSemidef → Q.mulVec (fun _ => (1 : ℝ)) = 0 →
        (∑ i, ∑ j, if 0 < Q i j then Q i j * d i j ^ 2 else 0) +
          c ^ 2 * (∑ i, ∑ j, if Q i j < 0 then Q i j * d i j ^ 2 else 0) ≤ 0 := by sorry

end GeometryOfGraphs.EuclidDist
