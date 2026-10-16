-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_triangleMass_surviving_le
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.Splitting.triangleMass_surviving_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:35:47.498243+00:00
-- url     : https://prove2.me/theorems/64b50c13-4839-4ca8-ae45-d3515a9d5cf6
-- title:
--   Triangles that survive a vertex splitting embed into the split graph
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$, let $\vec E(G)$ be its set of oriented edges $e=(e^-,e^+)$, $e^-\sim e^+$, with reversal $\bar e=(e^+,e^-)$, let $F:\vec E(G)\to\vec E(G)$ satisfy $F(e)^-=e^-$ for all $e$, and let $\mathrm{good}$ be a predicate on $\vec E(G)$. Let $H$ be the splitting graph on $\vec E(G)$: $a\sim_Hb$ if and only if some oriented edge $e$ satisfies $\mathrm{good}(e)$, $\mathrm{good}(\bar e)$, $F(e)=a$ and $F(\bar e)=b$.
--
--   An ordered triangle $t=(a,b,c)$ of $G$ (so $a\sim b$, $a\sim c$, $b\sim c$) *survives* if at each corner the two oriented edges leaving it are sent to the same copy,
--
--   $$
--   F(a,b)=F(a,c),\qquad F(b,a)=F(b,c),\qquad F(c,a)=F(c,b),
--   $$
--
--   and all six oriented edges $(a,b),(b,a),(a,c),(c,a),(b,c),(c,b)$ are good. For a simple graph $\Gamma$ on a finite set $X$ and $\omega:X\to\mathbb R$, let $T_\Gamma(\omega)=\sum_{\{x,y,z\}}\omega_x\omega_y\omega_z$ be the weighted triangle mass, the sum running over the triangles of $\Gamma$.
--
--   If $w:V\to\mathbb R$ is nonnegative, then
--
--   $$
--   \sum_{\substack{t=(a,b,c)\ \text{ordered triangle of }G\\ t\ \text{survives}}}w_aw_bw_c\ \le\ 6\,T_H(w\circ\pi),
--   $$
--
--   where $\pi(a)=a^-$ is the tail map, so that $(w\circ\pi)_a=w_{a^-}$.
--
--   Both sides count triangles with all six orientations, so the statement says that the triangle mass that survives the splitting is retained by the split graph. Combined with an estimate of the expected weight of the triangles that do not survive a random splitting, it shows that splitting loses only a small part of the triangle mass.
--
--   **Formalization Note** The left-hand side is `∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0`, and $T_H(w\circ\pi)$ is `triangleMass (graph F hF good) (w ∘ EdgeState.src)`, defined as one sixth of the sum of the weights of the ordered triangles.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Splitting.lean#L101-L140

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.Splitting.triangleMass_surviving_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (F : EdgeState G → EdgeState G) (hF : ∀ e, (F e).src = e.src)
    (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0) ≤
      6 * triangleMass (graph F hF good) (w ∘ EdgeState.src) := by sorry
