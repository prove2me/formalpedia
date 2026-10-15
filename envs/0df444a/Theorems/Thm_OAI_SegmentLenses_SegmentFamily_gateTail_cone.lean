-- Prove2me | Theorems.Thm_OAI_SegmentLenses_SegmentFamily_gateTail_cone
-- name    : OAI.SegmentLenses.SegmentFamily.gateTail_cone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:14:04.313694+00:00
-- url     : https://prove2.me/theorems/4c9059a2-699f-40d9-93fb-d751ab5e68e6
-- title:
--   A gate tail lies in the cone of descendants of its gate
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. A vertex $g$ is a *gate* of a finite set $H$ if $g\notin H$ and every $v<g$ lies in $H$. For a segment family $\mathcal F$, a finite set $H\subseteq V$ and a vertex $g\in V$, the *gate tail* $\tau_{\mathcal F,H}(g)$ is $S\setminus H$ if some member $S\in\mathcal F$ contains $g$ (this member is unique, since the members are pairwise disjoint), and $\emptyset$ otherwise.
--
--   Let $\mathcal F$ be a segment family, let $H\subseteq V$ be finite (not necessarily ancestral), and let $g$ be a gate of $H$. Then every element of the gate tail of $g$ is a descendant of $g$:
--   $$
--   v\in\tau_{\mathcal F,H}(g)\ \Longrightarrow\ g\le v .
--   $$
--
--   Distinct gates are incomparable, and in a tree order a vertex lying above two vertices makes them comparable. So the cones above distinct gates are pairwise disjoint, and with them the gate tails of distinct gates, even when the tails come from different segment families. This is the cone hypothesis of the cone reconstruction bound in the finite midpoint tail estimate.
--
--   **Formalization Note** `F.gateTail H g` selects the member containing $g$ with `Classical.choose`. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/GateRecovery.lean#L156-L170

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery

open OAI OAI.SegmentLenses OAI.SegmentLenses.SegmentFamily
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem OAI.SegmentLenses.SegmentFamily.gateTail_cone (F : SegmentFamily V) {H : Finset V} {g v : V}
    (hg : Gate H g) (hv : v ∈ F.gateTail H g) : g ≤ v := by sorry
