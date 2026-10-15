-- Prove2me | Theorems.Thm_OAI_ForestSpace_IsSegment_sdiff_before
-- name    : OAI.ForestSpace.IsSegment.sdiff_before
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:12:48.065992+00:00
-- url     : https://prove2.me/theorems/27d438fa-1cfd-4e6f-ae5c-53f6fcb587c8
-- title:
--   Removing $[b,g)$ from a segment of the form $[a,g)$ leaves a segment
-- statement:
--   Let $V$ be a finite partially ordered set. A *segment* is a finite set $S\subseteq V$ that is a chain and is order-convex ($a,b\in S$ and $a\le c\le b$ imply $c\in S$). For $a,g\in V$ write $[a,g)=\{v\in V:\ a\le v<g\}$.
--
--   **Theorem.** Let $a,b,g\in V$ and let $S$ be a segment with $S=[a,g)$. Then
--   $$
--   S\setminus[b,g)=\{v\in V:\ a\le v<g\ \text{and}\ b\not\le v\}
--   $$
--   is a segment.
--
--   No relation between $a$ and $b$ is assumed. When $a\le b<g$, the set $[b,g)$ is the terminal part of the path $[a,g)$ that ends just before $g$, and the theorem says that cutting it off leaves a segment. This is how the head $S\cap H=[a,g)$ of a segment is split into two disjoint segments, a selected terminal piece $L$ and the remainder $(S\cap H)\setminus L$, in the paired-correction estimate.
--
--   **Formalization Note** The interval $[a,g)$ is `before a g`, defined by filtering the finite type `V`; the segment hypothesis on $S$ is part of the statement (it holds automatically in a forest).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/FiniteGeometry.lean#L64-L78

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

theorem OAI.ForestSpace.IsSegment.sdiff_before {S : Finset V} (hS : IsSegment S) {a b g : V}
    (hSa : S = before a g) : IsSegment (S \ before b g) := by sorry
