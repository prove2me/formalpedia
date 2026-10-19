-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_segment_filter_head
-- name    : OAI.DiamondDistortion.Ancestry.segment_filter_head
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:44:13.774881+00:00
-- url     : https://prove2.me/theorems/d8ef1905-96d0-4f6c-b4d5-08302862bccd
-- title:
--   The part of an order interval inside a downward-closed set is an interval
-- statement:
--   Let $(\iota,\le)$ be an *ancestral order*: a partially ordered set in which the predecessors of every element form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$ (as for the ancestry order of a rooted forest). A *segment* is a finite set $S\subseteq\iota$ that is an order interval $S=[a,b]=\{v\in\iota: a\le v\le b\}$ for some $a\le b$; in particular a segment is nonempty and $a=\min S$ is its least element. A set $H\subseteq\iota$ is *ancestral* (a head) if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$.
--
--   Let $S$ be a segment and $H\subseteq\iota$ an ancestral set. If $S\cap H$ is nonempty, then it is again a segment:
--   $$
--   S\cap H\neq\emptyset\ \Longrightarrow\ S\cap H=[a',b']\ \text{ for some } a'\le b' .
--   $$
--
--   Cutting a segment by a head therefore leaves a piece that is still admissible in the segment norm of the ancestral order (whose test families consist of pairwise disjoint segments). Together with the companion statement for $S\setminus H$, this allows each member of a disjoint segment family to be split at a head without leaving the class of segments.
--
--   **Formalization Note** The ancestral order is the class `Ancestry`, segments are those of `A.segments` (the interval segment system of the order), and `A.Ancestral H` is downward closedness. The statement is phrased with `Finset.filter`, so $S\cap H$ is the finite set of elements of $S$ lying in $H$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L53-L74

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
variable {ι : Type*} [A : Ancestry ι]

theorem OAI.DiamondDistortion.Ancestry.segment_filter_head {S : Finset ι} (hS : A.segments.IsSegment S)
    {H : Set ι} (hH : A.Ancestral H) :
    (S.filter (· ∈ H)).Nonempty → A.segments.IsSegment (S.filter (· ∈ H)) := by sorry
