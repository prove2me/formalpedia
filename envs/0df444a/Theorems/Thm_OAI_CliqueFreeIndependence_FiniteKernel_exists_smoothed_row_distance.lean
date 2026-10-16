-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_exists_smoothed_row_distance
-- name    : OAI.CliqueFreeIndependence.FiniteKernel.exists_smoothed_row_distance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:39:51.700118+00:00
-- url     : https://prove2.me/theorems/a8ca81a8-fb52-4ab0-a460-d199fbae7763
-- title:
--   Entropy telescoping yields a smoothing step with small averaged row distances
-- statement:
--   Let $I$ be a finite set. A vector $p:I\to\mathbb R$ is a *probability vector* if $p_i\ge0$ for all $i$ and $\sum_ip_i=1$. For a weight vector $w$ with $w_i>0$ for all $i$ define the weighted entropy of $p$ and the total variation distance of $p,q$ by
--
--   $$
--   H_w(p)=\sum_{i\in I}p_i\log\frac{w_i}{p_i},\qquad d_{\mathrm{TV}}(p,q)=\frac12\sum_{i\in I}|p_i-q_i| ,
--   $$
--
--   where terms with $p_i=0$ are $0$. Let $P$ be a stochastic $I\times I$ matrix (every row $P_{i\cdot}$ is a probability vector), let $\pi$ be a probability vector that is stationary for $P$, i.e. $\sum_i\pi_iP_{ij}=\pi_j$ for all $j$, and let $\Lambda=\frac12(\mathrm{Id}+P)$ be the lazy version of $P$. For $j\in\mathbb N$ let $S_j=P\Lambda^j$ be the $j$-th smoothed kernel (so $S_0=P$), and for an $I\times I$ matrix $K$ put $\mathcal A(K)=\sum_i\pi_i\,H_w(K_{i\cdot})$.
--
--   Let $R$ be a positive integer and $D$ a real number with $\mathcal A(S_R)-\mathcal A(S_0)\le D$. Then there is an index $j$ with $0\le j<R$ such that
--
--   $$
--   \Big(\sum_{i\in I}\pi_i\sum_{z\in I}P_{iz}\,d_{\mathrm{TV}}\big((S_j)_{i\cdot},(S_j)_{z\cdot}\big)\Big)^2\le\frac{4D}{R}.
--   $$
--
--   If the averaged row entropy can grow by at most $D$ over $R$ smoothing steps, then at some intermediate step the smoothed rows at the two ends of a $P$-step are, on average, close in total variation. In the triangle-counting argument this is applied to the random walk on oriented edges to find a smoothing scale at which neighboring states have nearly the same smoothed distribution.
--
--   **Formalization Note** Kernels are `Matrix I I ℝ`, the row $K_{i\cdot}$ is `K i`, $S_j$ is `smoothed P j = P * lazy P ^ j` with `lazy P i j = ((if i = j then 1 else 0) + P i j) / 2`, and $\mathcal A$ is `avgEntropy π w`. The entropy uses Mathlib's `Real.log`, so a zero coordinate of $p$ contributes $0$. The bound $4D/R$ is computed in the reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean#L288-L310

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteKernel
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
open FiniteEntropy
variable {I : Type u} [Fintype I]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI

theorem OAI.CliqueFreeIndependence.FiniteKernel.exists_smoothed_row_distance {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P)
    {R : ℕ} (hR : 0 < R) {D : ℝ}
    (hD : avgEntropy π w (smoothed P R) - avgEntropy π w (smoothed P 0) ≤ D) :
    ∃ j < R, (∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z)) ^ 2 ≤
      4 * D / R := by sorry
