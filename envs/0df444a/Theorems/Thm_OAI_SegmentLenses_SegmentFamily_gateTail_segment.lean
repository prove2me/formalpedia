-- Prove2me | Theorems.Thm_OAI_SegmentLenses_SegmentFamily_gateTail_segment
-- name    : OAI.SegmentLenses.SegmentFamily.gateTail_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:12:51.877438+00:00
-- url     : https://prove2.me/theorems/62651b0e-ab5e-4fd5-81e5-819491247585
-- title:
--   The part of a family member lying outside an ancestral set is empty or a segment
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$. For a segment family $\mathcal F$, a finite set $H\subseteq V$ and a vertex $g\in V$, the *gate tail* $\tau_{\mathcal F,H}(g)$ is defined as follows. If some member $S\in\mathcal F$ contains $g$, then $\tau_{\mathcal F,H}(g)=S\setminus H$; this member is unique, since the members are pairwise disjoint. Otherwise $\tau_{\mathcal F,H}(g)=\emptyset$.
--
--   Let $\mathcal F$ be a segment family and $H\subseteq V$ finite and ancestral. Then for every vertex $g\in V$,
--   $$
--   \tau_{\mathcal F,H}(g)=\emptyset\qquad\text{or}\qquad\tau_{\mathcal F,H}(g)\ \text{is a segment}.
--   $$
--
--   Thus removing an ancestral set from a member of a segment family leaves an admissible piece for segment-norm estimates. In the finite midpoint tail bound, gate tails are the pieces in the cone reconstruction estimate, and this theorem supplies its hypothesis that every piece is empty or a segment.
--
--   **Formalization Note** `F.gateTail H g` selects the member containing $g$ with `Classical.choose`. The statement holds for every $g$, whether or not it is a gate. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/GateRecovery.lean#L138-L154

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

theorem OAI.SegmentLenses.SegmentFamily.gateTail_segment (F : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (g : V) :
    F.gateTail H g = ∅ ∨ SegmentSystem.isSegment (F.gateTail H g) := by sorry
