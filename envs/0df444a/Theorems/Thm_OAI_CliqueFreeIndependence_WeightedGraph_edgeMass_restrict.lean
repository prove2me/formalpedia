-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_restrict
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_restrict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:18:43.408648+00:00
-- url     : https://prove2.me/theorems/c01b54b8-531d-4c2d-9633-7f8ed127d970
-- title:
--   Edge mass of a weight vector restricted to a vertex set
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, let $w:V\to\mathbb{R}$ be a real weight function and let $A\subseteq V$. Write $\mathbf 1_Aw$ for the restriction of $w$ to $A$, i.e. $(\mathbf 1_Aw)_v=w_v$ for $v\in A$ and $(\mathbf 1_Aw)_v=0$ otherwise. For $S,T\subseteq V$ define the cross mass
--   $c_G(w;S,T)=\sum_{u\in S}\sum_{v\in T}\mathbf 1[u\sim v]\,w_uw_v$, and recall that the edge mass is $E_G(w)=\tfrac12c_G(w;V,V)$. Then
--
--   $$
--   E_G(\mathbf 1_Aw)=\frac12\,c_G(w;A,A)=\frac12\sum_{u\in A}\sum_{v\in A}\mathbf 1[u\sim v]\,w_uw_v .
--   $$
--
--   Equivalently, $E_G(\mathbf 1_Aw)$ is the sum of $w_uw_v$ over the edges $\{u,v\}$ of $G$ with both endpoints in $A$. This identity translates between restricted weight vectors and cross masses, and is the starting point for computing edge masses of closed neighbourhoods, of induced subgraphs and of multiplier vectors supported on a set.
--
--   **Formalization Note** In Lean the restriction is `restrict A w` and the cross mass is `crossMass G w A A`; $A$ is a `Finset V` and $w$ is arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean#L36-L57

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u
open Lottery
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_restrict (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    edgeMass G (restrict A w) = crossMass G w A A / 2 := by sorry
