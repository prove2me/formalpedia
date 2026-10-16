-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_projection
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.Splitting.projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:34:28.257311+00:00
-- url     : https://prove2.me/theorems/be57180a-49e9-4569-b44d-883123de3dc5
-- title:
--   The vertex-splitting graph projects onto the original graph injectively on oriented edges
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$ (not necessarily finite), with adjacency $u\sim v$. Let $\vec E(G)$ be its set of oriented edges $e=(e^-,e^+)$, $e^-\sim e^+$, with reversal $\bar e=(e^+,e^-)$. Let $F:\vec E(G)\to\vec E(G)$ preserve tails, $F(e)^-=e^-$ for every $e$ (so $F$ assigns to each oriented edge leaving $u$ a copy of $u$, itself labelled by an oriented edge leaving $u$), and let $\mathrm{good}$ be any predicate on oriented edges. The *splitting graph* $H=H(F,\mathrm{good})$ has vertex set $\vec E(G)$, and $a,b\in\vec E(G)$ are adjacent in $H$ if and only if some oriented edge $e$ of $G$ satisfies
--
--   $$
--   \mathrm{good}(e),\qquad\mathrm{good}(\bar e),\qquad F(e)=a,\qquad F(\bar e)=b .
--   $$
--
--   Let $\pi:\vec E(G)\to V$, $\pi(a)=a^-$, be the tail map. Then $\pi$ is an edge projection from $H$ to $G$:
--
--   1. $\pi$ maps edges to edges: if $a\sim_Hb$ then $\pi(a)\sim_G\pi(b)$;
--   2. $\pi$ is injective on oriented edges: if $a\sim_Hb$, $c\sim_Hd$, $\pi(a)=\pi(c)$ and $\pi(b)=\pi(d)$, then $a=c$ and $b=d$.
--
--   The splitting graph replaces each vertex $u$ of $G$ by several copies and keeps an edge $uv$ only between the copy chosen at $u$ for $v$ and the copy chosen at $v$ for $u$. Because $\pi$ is injective on oriented edges, for nonnegative weights $w$ on $V$ the pulled-back weights $w_{a^-}$ give $H$ no larger edge mass than $G$, no larger neighborhood masses than at the corresponding vertices of $G$, and no larger cross masses than between the projected sets in $G$, which makes vertex splitting compatible with the estimates of the triangle-counting argument.
--
--   **Formalization Note** Oriented edges are `EdgeState G`, $H$ is `Splitting.graph F hF good`, where `hF` is the tail-preservation hypothesis (it is needed to show that $H$ has no loops), and the conclusion is the structure `EdgeProjection H G EdgeState.src`, whose two fields are the two claims.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Splitting.lean#L38-L56

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.Splitting
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
variable {G : SimpleGraph V}

omit [Fintype V] in
theorem OAI.CliqueFreeIndependence.WeightedGraph.Splitting.projection (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop) :
    EdgeProjection (graph F hF good) G EdgeState.src := by sorry
