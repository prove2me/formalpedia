-- Prove2me | Theorems.Thm_OAI_ForestSpace_exists_head_approx
-- name    : OAI.ForestSpace.exists_head_approx
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:21:47.982878+00:00
-- url     : https://prove2.me/theorems/df01b30a-e62c-43f6-bc73-e96358b64d64
-- title:
--   Finite ancestral heads approximate every element of the coordinate subspace of $J(V)^*$
-- statement:
--   Let $(V,\le)$ be a partially ordered set in which every element has finitely many predecessors (the set $\{w\in V: w\le v\}$ is finite for every $v\in V$). Let $J(V)$ be the completion of the finitely supported functions $u:V\to\mathbb{R}$ under the disjoint-segment norm $\|u\|=\sup\big(\sum_i(\sum_{v\in S_i}u(v))^2\big)^{1/2}$, the supremum running over finite families of pairwise disjoint segments $S_i$ (finite order-convex chains), and let $J(V)^*$ be its continuous dual. Write $e_v$ for the unit vector at $v$ and $e_v^*\in J(V)^*$ for the coordinate functional, $e_v^*(u)=u(v)$ on finitely supported $u$. The *coordinate subspace* $X(V)\subseteq J(V)^*$ is the norm closure of the linear span of $\{e_v^*: v\in V\}$.
--
--   For a lower set $H\subseteq V$ (if $w\le v\in H$ then $w\in H$), the restriction $u\mapsto u\mathbf 1_H$ does not increase the segment norm and extends to a contraction $\Pi_H$ of $J(V)$; the head projection on the dual is $P_Hx=x\circ\Pi_H$. When $H$ is finite, $P_Hx=\sum_{v\in H}x(e_v)\,e_v^*$, so $P_H$ maps $X(V)$ into itself. The theorem states: for every $x\in X(V)$ and every $\varepsilon>0$ there is a finite lower set $H\subseteq V$ such that
--
--   $$
--   \|x-P_Hx\|<\varepsilon .
--   $$
--
--   Thus every element of the coordinate subspace is approximated in norm by its restrictions to finite ancestral heads. This reduces estimates for elements of $X(V)$ to finitely many coordinates on a head plus a remainder that lives on the complementary tail. For the finite-height forest of the main theorem, where $X$ is the whole dual, it is the density step behind the lens inequality and the lower bound for the averaged asymptotic midpoint modulus.
--
--   **Formalization Note** `X V` is the subtype of the closed submodule `coordinateSubspace V` of `FullDual V = StrongDual ℝ (J V)`, with the inherited norm, and `PX H hH` is `P H hH` restricted to `X V` for `H : Finset V` with `hH : IsLowerSet (H : Set V)`. No forest condition on $V$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Projections.lean#L164-L180

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.exists_head_approx (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (x : X V) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Finset V, ∃ hH : IsLowerSet (H : Set V), ‖x - PX H hH x‖ < ε := by sorry
