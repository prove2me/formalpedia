-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_reversible
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_reversible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:44:52.392993+00:00
-- url     : https://prove2.me/theorems/2cbcf537-2ad7-4750-9f80-3a0674d9ec1b
-- title:
--   The local walk is reversible with respect to the triangle-weighted edge law
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with at least one edge, and let $w:V\to\mathbb{R}$ satisfy $w(u)>0$ for all $u\in V$. Write $N(u)$ for the neighbourhood of $u$, $W(u,v)=\sum_{z\in N(u)\cap N(v)}w(z)$ for the weight of the common neighbourhood, and $\vec E(G)$ for the set of oriented edges $(u,v)$ with $u\sim v$. The *local walk* is the kernel $T$ on $\vec E(G)$ with $T\big((u,v),(u',v')\big)=w(v')/W(u,v)$ if $u'=u$ and $v\sim v'$, and $0$ otherwise. Its *edge law* is
--
--   $$
--   \pi(u,v)=\frac{w(u)\,w(v)\,W(u,v)}{Z},\qquad Z=\sum_{(u,v)\in\vec E(G)}w(u)\,w(v)\,W(u,v).
--   $$
--
--   Assume that $W(u,v)>0$ for every edge $uv$ of $G$. Then $T$ is reversible with respect to $\pi$: for all oriented edges $e,f\in\vec E(G)$,
--
--   $$
--   \pi(e)\,T(e,f)=\pi(f)\,T(f,e).
--   $$
--
--   Expanding $W$, the normalizer is $Z=\sum w(u)w(v)w(v')$ over all ordered triangles $(u,v,v')$ of $G$, and $\pi(u,v)\,T\big((u,v),(u,v')\big)=w(u)w(v)w(v')/Z$ is the normalized weight of the ordered triangle $(u,v,v')$; reversibility is the symmetry of this weight under exchanging $v$ and $v'$. Since $T$ is also stochastic, it follows that $\pi$ is a stationary distribution of the local walk, which is what makes entropy-increment and telescoping arguments for the smoothed walk available.
--
--   **Formalization Note** $\vec E(G)$ is `EdgeState G`, $T$ is `transition G w`, $\pi$ is `law G w` and $Z$ is `normalizer G w`; `Reversible π P` means $\pi_iP_{ij}=\pi_jP_{ji}$ for all $i,j$. The assumption that $G$ has an edge is the instance `[Nonempty (EdgeState G)]`; it makes $Z>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/LocalWalk.lean#L91-L104

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)
variable {G w}

theorem OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_reversible [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) :
    Reversible (law G w) (transition G w) := by sorry
