-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_EdgeProjection_crossMass_edge_sum
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection.crossMass_edge_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:33:08.831362+00:00
-- url     : https://prove2.me/theorems/ee0605c6-8eae-473d-a75c-2c400bb5e7cd
-- title:
--   Weighted cross mass as a sum over oriented edges
-- statement:
--   Let $H$ be a simple graph on a finite vertex set $U$, with adjacency $a\sim b$ and neighborhoods $N(a)$. An *oriented edge* of $H$ is a pair $e=(e^-,e^+)$ with $e^-\sim e^+$, and $\vec E(H)$ is the finite set of oriented edges. For $w:U\to\mathbb R$ and $A,B\subseteq U$ the *cross mass* is
--
--   $$
--   e_w(A,B)=\sum_{a\in A}\ \sum_{b\in B,\ a\sim b}w_a\,w_b .
--   $$
--
--   Then for every real-valued $w$ (no sign condition) and all $A,B\subseteq U$,
--
--   $$
--   e_w(A,B)=\sum_{e\in\vec E(H)}\mathbf 1\big[e^-\in A,\ e^+\in B\big]\,w_{e^-}w_{e^+}.
--   $$
--
--   Writing cross masses as sums over oriented edges makes them easy to compare along maps of graphs that are injective on oriented edges; this is how cross masses and edge masses of a graph obtained by splitting vertices are bounded by those of the original graph.
--
--   **Formalization Note** Oriented edges are the subtype `EdgeState H` of `U × U`, with endpoints `src` and `dst`, and $e_w(A,B)$ is `crossMass H w A B`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Projection.lean#L55-L71

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
variable {U : Type v} [Fintype U]
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

theorem OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection.crossMass_edge_sum (H : SimpleGraph U) (w : U → ℝ) (A B : Finset U) :
    crossMass H w A B =
      ∑ e : EdgeState H, if e.src ∈ A ∧ e.dst ∈ B then w e.src * w e.dst else 0 := by sorry
