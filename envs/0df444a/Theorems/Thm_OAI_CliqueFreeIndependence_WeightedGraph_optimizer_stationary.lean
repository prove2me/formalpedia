-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.optimizer_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:16:24.459569+00:00
-- url     : https://prove2.me/theorems/c32f97be-664b-4089-a20c-93b13f7b079a
-- title:
--   Stationarity of potential maximizers: $w_v=e^{-N_v(w)}$
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ (no loops, so $u\sim v$ implies $u\ne v$), and write $N(v)$ for the set of neighbours of a vertex $v$. For a weight function $w:V\to\mathbb{R}$ and $S\subseteq V$ put $w(S)=\sum_{v\in S}w_v$, and let $N_v(w)=w(N(v))=\sum_{u\sim v}w_u$ be the neighbour mass of $v$. The edge mass of $w$ is
--   $E_G(w)=\tfrac12\sum_{u\in V}\sum_{v\in V}\mathbf 1[u\sim v]\,w_uw_v=\sum_{\{u,v\}\in E(G)}w_uw_v,$
--   and the potential of $w$ is
--   $\Phi_G(w)=\sum_{v\in V}\varphi(w_v)-E_G(w)$, where $\varphi(t)=t\,(1-\log t)$ ($\log$ is the natural logarithm) and $\varphi(0)=0$. A weight function $w$ is called an *optimizer* for $G$ if $w_v\ge0$ for every $v$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q:V\to\mathbb{R}$ with $q_v\ge0$ for all $v$; that is, $w$ maximizes $\Phi_G$ over the nonnegative orthant.
--
--   If $w$ is an optimizer for $G$, then for every vertex $v\in V$
--
--   $$
--   \log\frac{1}{w_v}=N_v(w),\qquad\text{equivalently}\qquad w_v=e^{-N_v(w)}.
--   $$
--
--   Precisely, the statement asserts the three facts:
--   1. $w_v>0$;
--   2. $\log(1/w_v)=N_v(w)$;
--   3. $w_v\le1$.
--
--   This is the first-order (fixed-point) characterization of a maximizer of the potential: every vertex carries strictly positive weight, and that weight is exponentially small in the total weight of its neighbourhood. It is the basic input for all further estimates on optimizers, such as their total weight, their edge mass and the cost of deleting vertex sets.
--
--   **Formalization Note** The edge mass is `edgeMass G w = crossMass G w univ univ / 2`, the vertex summand is `vertexPotential t = t * (1 - Real.log t)` (Lean's convention $\log 0=0$ makes it vanish at $t=0$), the potential is `potential G w`, and `IsOptimizer G w` is the maximality property described above, quantified over all nonnegative real-valued functions on $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Optimizer.lean#L179-L216

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.optimizer_stationary {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w) (v : V) :
    0 < w v ∧ Real.log (1/w v) = neighborMass G w v ∧ w v ≤ 1 := by sorry
