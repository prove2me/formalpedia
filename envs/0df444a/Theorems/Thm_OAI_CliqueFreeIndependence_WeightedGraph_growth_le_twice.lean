-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_growth_le_twice
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.growth_le_twice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:27:58.076255+00:00
-- url     : https://prove2.me/theorems/00aa75bc-1a70-4e76-8f23-56fd28fceb98
-- title:
--   Linear bound for the growth function: $g_x(s)\le2x\,(s+e^{-x})$
-- statement:
--   For real numbers $x$ and $s\ge0$ define the growth function
--   $g_x(s)=s\bigl(x+\max\{0,\log(1/s)\}\bigr)$ for $s>0$ and $g_x(0)=0$, where $\log$ is the natural logarithm. Explicitly, $g_x(s)=s(x-\log s)$ for $0<s\le1$ and $g_x(s)=sx$ for $s\ge1$.
--
--   If $x\ge1$ and $s\ge0$, then
--
--   $$
--   g_x(s)\le 2x\,\bigl(s+e^{-x}\bigr).
--   $$
--
--   Thus, up to the additive error $2xe^{-x}$, the growth function is at most linear in $s$ with slope $2x$: the logarithmic factor $\log(1/s)$ never exceeds $x$ once $s\ge e^{-x}$, and below that point monotonicity takes over. This linearization turns a cross-mass bound with profile $g_x$ into a bound that is linear in the mass of a set, which is used in conditional estimates of bad events inside neighbourhoods.
--
--   **Formalization Note** In Lean `growth x s = s * (x + max 0 (Real.log (1 / s)))`, with $g_x(0)=0$ by the conventions $1/0=0$ and $\log0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/EdgeState.lean#L110-L127

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.growth_le_twice {x s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) :
    growth x s ≤ 2 * x * (s + Real.exp (-x)) := by sorry
