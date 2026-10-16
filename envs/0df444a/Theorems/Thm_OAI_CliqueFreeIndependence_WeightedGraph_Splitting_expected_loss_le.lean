-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_expected_loss_le
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.Splitting.expected_loss_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:58:32.930956+00:00
-- url     : https://prove2.me/theorems/3b86537a-404b-4748-bc0a-99326ca72987
-- title:
--   Expected triangle loss of a random splitting map is bounded by corner and incidence losses
-- statement:
--   Let $G$ be a finite simple graph on a finite vertex set $V$ with at least one edge, write $u\sim v$ for adjacency and $N(u)$ for the neighbourhood of $u$, and let $w\colon V\to\mathbb{R}$ satisfy $w_u>0$ for every $u$. Put $c_w(u,v)=\sum_{z\in N(u)\cap N(v)}w_z$ (the common-neighbour mass) and assume $c_w(u,v)>0$ for every edge $uv$.
--
--   Let $\vec E$ be the finite set of oriented edges $e=(u,v)$ of $G$, with source $s(e)=u$, target $t(e)=v$ and reversal $\bar e=(v,u)$. Let $\mathcal T$ be the set of ordered triangles $\tau=(\tau_1,\tau_2,\tau_3)$ of pairwise adjacent vertices, with weight $w(\tau)=w_{\tau_1}w_{\tau_2}w_{\tau_3}$ and oriented sides $\tau_{12}=(\tau_1,\tau_2)$, $\tau_{13}=(\tau_1,\tau_3)$, $\tau_{23}=(\tau_2,\tau_3)$. The local walk is the kernel on $\vec E$ given by
--   $$
--   P(e,f)=\begin{cases}\dfrac{w_{t(f)}}{c_w\big(s(e),t(e)\big)}, & \text{if } s(f)=s(e)\text{ and }t(e)\sim t(f),\\ 0, & \text{otherwise};\end{cases}
--   $$
--   from $(u,v)$ it moves to $(u,z)$, where $z$ is a common neighbour of $u$ and $v$ chosen with probability proportional to $w_z$. Its normaliser and stationary law are
--   $$
--   Z=\sum_{e\in\vec E}w_{s(e)}\,w_{t(e)}\,c_w\big(s(e),t(e)\big),\qquad \lambda(e)=\frac{w_{s(e)}\,w_{t(e)}\,c_w\big(s(e),t(e)\big)}{Z}.
--   $$
--   For vectors $p,p'$ indexed by $\vec E$, $\mathrm{tv}(p,p')=\frac12\sum_{y}|p_y-p'_y|$ is the total variation distance, and $K(e,\cdot)$ denotes the row of a matrix $K$ indexed by $e$.
--
--   For a map $F\colon\vec E\to\vec E$ and a predicate $\mathrm{good}$ on $\vec E$, an ordered triangle $\tau$ survives if the three corner agreements
--   $$
--   F(\tau_{12})=F(\tau_{13}),\qquad F(\bar\tau_{12})=F(\tau_{23}),\qquad F(\bar\tau_{13})=F(\bar\tau_{23})
--   $$
--   hold (at each corner the two sides leaving that corner are sent to the same oriented edge) and all six oriented sides $\tau_{12},\bar\tau_{12},\tau_{13},\bar\tau_{13},\tau_{23},\bar\tau_{23}$ are good. For a proposition $Q$ let $\mathbf 1[\neg Q]$ be $0$ if $Q$ holds and $1$ otherwise.
--
--   Let $K=(K(i,y))_{i,y\in\vec E}$ be a real matrix and let $q$ be a probability distribution on the finite set of all maps $F\colon\vec E\to\vec E$ such that for all $i,j,y\in\vec E$
--   $$
--   \sum_{F:\,F(i)=y}q(F)=K(i,y),\qquad\sum_{F:\,F(i)\neq F(j)}q(F)\le2\,\mathrm{tv}\big(K(i,\cdot),K(j,\cdot)\big);
--   $$
--   that is, under $q$ the image $F(i)$ has law $K(i,\cdot)$, and the event $F(i)\neq F(j)$ has probability at most twice the total variation distance between the corresponding rows. Finally, for every map $F$ let $\mathrm{good}_F$ be a predicate on $\vec E$, and let $b$ be a relation on $\vec E\times\vec E$ with $\mathrm{good}_F(e)\iff b\big(e,F(e)\big)$ for all $F$ and $e$. Then
--   $$
--   \sum_{F}q(F)\sum_{\tau\in\mathcal T}w(\tau)\,\mathbf 1\big[\neg\,\tau\text{ survives for }(F,\mathrm{good}_F)\big]\;\le\;Z\Big(6\sum_{e\in\vec E}\lambda(e)\sum_{z\in\vec E}P(e,z)\,\mathrm{tv}\big(K(e,\cdot),K(z,\cdot)\big)+6\sum_{e\in\vec E}\lambda(e)\sum_{y\in\vec E}K(e,y)\,\mathbf 1\big[\neg\,b(e,y)\big]\Big).
--   $$
--
--   The left side is the expected weight of the ordered triangles destroyed when a random map $F\sim q$ is used to split the vertices of $G$. The right side depends only on $K$. It is a corner loss, the $\lambda$-average total variation between the rows of $K$ at the two ends of one step of the local walk, plus an incidence loss, the $\lambda$-average probability that the image of an oriented edge is inadmissible. This averaging estimate is what guarantees a vertex splitting that keeps most of the triangle weight.
--
--   **Formalization Note** Oriented edges and ordered triangles are the subtypes `EdgeState G` and `TriangleState G`, and the hypothesis `Nonempty (EdgeState G)` says that $G$ has an edge. `Law q` means $q\ge0$ and $\sum_Fq(F)=1$. The matrix $K$ is a `Kernel (EdgeState G)`, an arbitrary real square matrix that is not assumed stochastic; the marginal identity forces its rows to be probability vectors. The indicator $\mathbf 1[\neg Q]$ is `bad Q`, survival is `Survives F (good F) t`, and $Z$, $\lambda$, $P$ are `normalizer G w`, `law G w` and `transition G w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/SplittingLoss.lean#L90-L155

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
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.Splitting
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
open FiniteCoupling
variable {G : SimpleGraph V}
open FiniteEntropy FiniteKernel LocalWalk

theorem OAI.CliqueFreeIndependence.WeightedGraph.Splitting.expected_loss_le [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) {q : (EdgeState G → EdgeState G) → ℝ}
    (hq : Law q) (hm : ∀ i y, (∑ F, if F i = y then q F else 0) = K i y)
    (hp : ∀ i j, (∑ F, if F i ≠ F j then q F else 0) ≤ 2 * tv (K i) (K j))
    (good : (EdgeState G → EdgeState G) → EdgeState G → Prop)
    (b : EdgeState G → EdgeState G → Prop)
    (hb : ∀ F e, good F e ↔ b e (F e)) :
    (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t)) ≤
      normalizer G w *
        (6 * (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) +
         6 * (∑ e, law G w e * ∑ y, K e y * bad (b e y))) := by sorry
