-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_growth_mono
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.growth_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:27:28.553414+00:00
-- url     : https://prove2.me/theorems/082b3031-2957-4a3a-a622-f37246e47479
-- title:
--   The growth function $g_x(s)=s\,(x+\max\{0,\log(1/s)\})$ is nondecreasing for $x\ge1$
-- statement:
--   For real numbers $x$ and $s\ge0$ define the growth function
--   $g_x(s)=s\bigl(x+\max\{0,\log(1/s)\}\bigr)$ for $s>0$ and $g_x(0)=0$, where $\log$ is the natural logarithm. Explicitly, $g_x(s)=s(x-\log s)$ for $0<s\le1$ and $g_x(s)=sx$ for $s\ge1$.
--
--   If $x\ge1$, then $g_x$ is nondecreasing on $[0,\infty)$: for all real $a,b$,
--
--   $$
--   0\le a\le b\ \Longrightarrow\ g_x(a)\le g_x(b).
--   $$
--
--   The function $g_x$ is the growth profile in the weighted cross-mass condition used for clique-free graphs, which bounds the weighted number of edges between vertex sets $S$ and $T$ of mass at most $e^{x}$ by a constant times $g_x(w(S))$. Monotonicity lets such bounds be transferred from a set to any set of larger mass.
--
--   **Formalization Note** In Lean `growth x s = s * (x + max 0 (Real.log (1 / s)))` is defined for all real $s$; at $s=0$ Lean's conventions $1/0=0$ and $\log0=0$ give $g_x(0)=0$, matching the continuous extension. The statement is `MonotoneOn (growth x) (Set.Ici 0)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/EdgeState.lean#L84-L108

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance] OAI.CliqueFreeIndependence.WeightedGraph.edgeStateDecEq

theorem OAI.CliqueFreeIndependence.WeightedGraph.growth_mono {x : ℝ} (hx : 1 ≤ x) : MonotoneOn (growth x) (Set.Ici 0) := by sorry
