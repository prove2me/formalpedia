-- Prove2me | Theorems.Thm_OAI_ForestSpace_IsSegment_head_eq_before
-- name    : OAI.ForestSpace.IsSegment.head_eq_before
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:12:20.417559+00:00
-- url     : https://prove2.me/theorems/79c451cc-b2f4-44e4-99e8-c5413029bc0d
-- title:
--   A segment through a gate meets the lower set in an interval ending just before the gate
-- statement:
--   Let $V$ be a finite partially ordered set and $H\subseteq V$ a lower set ($w\le v\in H$ implies $w\in H$). A *gate* of $H$ is an element $g\notin H$ all of whose strict predecessors lie in $H$ (that is, $v<g$ implies $v\in H$); minimal elements of $V$ outside $H$ are gates. A *segment* is a finite set $S\subseteq V$ that is a chain and is order-convex ($a,b\in S$, $a\le c\le b$ imply $c\in S$). For $a,g\in V$ write $[a,g)=\{v\in V:\ a\le v<g\}$.
--
--   **Theorem.** Let $S$ be a segment, let $g$ be a gate of $H$ with $g\in S$, and assume that $S$ contains at least one element of $H$. Then there is $a\in V$ with $a<g$ such that
--   $$
--   S\cap H=[a,g)=\{v\in V:\ a\le v<g\}.
--   $$
--
--   So the part of a segment that lies in the ancestral set $H$, when the segment passes through a gate $g$, is an initial piece ending immediately before $g$. This normal form is used in the paired-correction estimate to compare the sum over $S\cap H$ of a function supported on $H$ with sums over intervals $[a,g)$, which depend only on the start $a$ and the gate $g$ and not on the segment.
--
--   **Formalization Note** The interval $[a,g)$ is `before a g`, obtained by filtering the finite type `V` (hence the `Fintype V` assumption), and $S\cap H$ is the filter of $S$ by membership in $H$. The gate condition is `Gate H g`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/FiniteGeometry.lean#L42-L62

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [PartialOrder V]

theorem OAI.ForestSpace.IsSegment.head_eq_before {H : Set V} (hH : IsLowerSet H)
    {S : Finset V} (hS : IsSegment S) {g : V} (hg : Gate H g) (hgs : g ∈ S)
    (hp : ∃ a ∈ S, a ∈ H) :
    ∃ a, a < g ∧ S.filter (· ∈ H) = before a g := by sorry
