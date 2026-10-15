-- Prove2me | Theorems.Thm_OAI_SegmentLenses_split_interval
-- name    : OAI.SegmentLenses.split_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:02:06.707561+00:00
-- url     : https://prove2.me/theorems/9b558677-4d9a-4f20-9347-34be29414dad
-- title:
--   Splitting an ancestry interval at an intermediate vertex of a tree order
-- statement:
--   Let $V$ be a partially ordered set, where $a\le b$ is read as "$a$ is an ancestor of $b$". Assume that every order interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and that the order is a *tree order*: any two ancestors of a common vertex are comparable, that is, $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Write $[a,c)=\{v\in V:\ a\le v<c\}$ for the half-open interval.
--
--   If $a\le c$ and $c\le b$, then
--   $$
--   [a,c)\cup[c,b]=[a,b].
--   $$
--
--   The two pieces are also disjoint, since $v<c$ and $c\le v$ cannot hold together. So every interval of a tree order splits at an intermediate vertex $c$ into the part strictly before $c$ and the part from $c$ on, and sums of a function over an ancestry interval split additively at a cut point. This is the basic step behind the split-gain estimates for segment norms on trees. The tree-order hypothesis is essential: in a general partial order the identity can fail when some vertex of $[a,b]$ is incomparable with $c$.
--
--   **Formalization Note** The identity is stated for `Finset.Ico a c`, `Finset.Icc c b` and `Finset.Icc a b` in a `LocallyFiniteOrder` with the `TreeOrder` class. Decidable equality, a segment system and the `IntervalSegments` assumption (segments are exactly the intervals) are present as section instance arguments but play no role in this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean#L121-L137

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem OAI.SegmentLenses.split_interval {a c b : V} (hac : a ≤ c) (hcb : c ≤ b) :
    Finset.Ico a c ∪ Finset.Icc c b = Finset.Icc a b := by sorry
