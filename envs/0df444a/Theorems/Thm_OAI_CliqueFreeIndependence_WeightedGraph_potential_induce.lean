-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_potential_induce
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.potential_induce
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:22:54.30867+00:00
-- url     : https://prove2.me/theorems/9e581c7b-5ba9-41e3-a298-0671ac7a3582
-- title:
--   The potential on an induced subgraph equals the potential of the restricted weights
-- statement:
--   For a simple graph $H$ on a finite vertex set $U$ and a weight function $x:U\to\mathbb{R}$, let $E_H(x)=\sum_{\{u,u'\}\in E(H)}x_ux_{u'}$ be the edge mass and
--   $\Phi_H(x)=\sum_{u\in U}\varphi(x_u)-E_H(x)$ the potential, where $\varphi(t)=t\,(1-\log t)$ with $\varphi(0)=0$.
--
--   Let $G$ be a simple graph on a finite vertex set $V$, let $w:V\to\mathbb{R}$ and let $A\subseteq V$. Write $G[A]$ for the subgraph of $G$ induced on the vertex set $A$, $w|_A$ for the restriction of $w$ to the vertices of $A$, and $\mathbf 1_Aw$ for the weight function on $V$ that equals $w$ on $A$ and $0$ outside $A$. Then
--
--   $$
--   \Phi_{G[A]}\bigl(w|_A\bigr)=\Phi_G\bigl(\mathbf 1_Aw\bigr).
--   $$
--
--   Thus deleting the vertices outside $A$ from the graph and setting their weights to zero are equivalent operations for the potential. This lets potentials of restricted weight vectors on $G$ be compared with potentials, and in particular optimizers, of induced subgraphs, as needed when the greedy independent-set argument recurses on the graph that remains after a closed neighbourhood has been removed.
--
--   **Formalization Note** The induced subgraph is `G.induce (A : Set V)`, whose vertex type is the subtype of elements of $A$, and $w|_A$ is `fun v ↦ w v` on that subtype. The vertex summand uses Lean's `Real.log`, for which $\log 0=0$ (and $\log t=\log|t|$), so $\varphi(0)=0$; the identity holds for every real-valued $w$, with no sign assumption.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Deletion.lean#L91-L112

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.potential_induce (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    potential (G.induce (A : Set V)) (fun v ↦ w v) = potential G (restrict A w) := by sorry
