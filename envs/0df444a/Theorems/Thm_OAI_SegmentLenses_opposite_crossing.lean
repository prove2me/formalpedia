-- Prove2me | Theorems.Thm_OAI_SegmentLenses_opposite_crossing
-- name    : OAI.SegmentLenses.opposite_crossing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:03:43.131893+00:00
-- url     : https://prove2.me/theorems/3fc7aa69-82ba-4f95-87f7-e5a926ca17ef
-- title:
--   Opposite-sign boundary sums of two segment families at gates are paid for by their slacks
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For finitely supported $p:V\to\mathbb{R}$ and finite $S\subseteq V$ put $p(S)=\sum_{v\in S}p(v)$. The family seminorm of a segment family $\mathcal F$ and the segment norm are
--   $$
--   \|p\|_{\mathcal F}=\Big(\sum_{S\in\mathcal F}p(S)^2\Big)^{1/2},\qquad\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\|p\|_{\mathcal F}.
--   $$
--   A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$. A vertex $g$ is a *gate* of a finite set $H$ if $g\notin H$ and every $v<g$ lies in $H$. The boundary sum of $\mathcal F$ at $g\in V$ is
--   $$
--   \partial_{\mathcal F}p(g)=\sum_{S\in\mathcal F,\ g\in S}p(S),
--   $$
--   the total of $p$ over the member of $\mathcal F$ containing $g$, or $0$ if no member contains $g$.
--
--   Let $\mathcal F$ and $\mathcal F'$ be segment families, let $H\subseteq V$ be finite and ancestral, let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$, and let $G\subseteq V$ be a finite set all of whose elements are gates of $H$. Then
--   $$
--   \sum_{g\in G}\Big(\big|\partial_{\mathcal F}p(g)\,\partial_{\mathcal F'}p(g)\big|-\partial_{\mathcal F}p(g)\,\partial_{\mathcal F'}p(g)\Big)\le\Big(\|p\|_{\mathrm{seg}}^2-\|p\|_{\mathcal F}^2\Big)+\Big(\|p\|_{\mathrm{seg}}^2-\|p\|_{\mathcal F'}^2\Big).
--   $$
--
--   Since $|z|-z$ equals $2|z|$ for $z<0$ and $0$ otherwise, the left-hand side is twice the sum of $|\partial_{\mathcal F}p(g)\,\partial_{\mathcal F'}p(g)|$ over the gates at which the two boundary sums have strictly opposite signs. The quantities $\|p\|_{\mathrm{seg}}^2-\|p\|_{\mathcal F}^2\ge0$ are the slacks of the two families. So sign disagreements of two families at the gates of $H$ are paid for by their slacks. In the finite midpoint tail bound this is applied to every pair of families drawn from a finite law, and controls how much the averaged absolute boundary sums at the gates exceed the averaged signed ones.
--
--   **Formalization Note** The boundary sum is `F.boundary p g`, the family seminorm is `F.seminorm p`, and the segment norm is `segmentSeminorm V p`. The support condition is `p.support ⊆ H`, and the sum runs over the elements of the finset `G`. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean#L428-L504

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem OAI.SegmentLenses.opposite_crossing (F F' : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (p : V →₀ ℝ) (hp : p.support ⊆ H)
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, (|F.boundary p g.val * F'.boundary p g.val| -
      F.boundary p g.val * F'.boundary p g.val)) ≤
      (segmentSeminorm V p ^ 2 - F.seminorm p ^ 2) +
      (segmentSeminorm V p ^ 2 - F'.seminorm p ^ 2) := by sorry
