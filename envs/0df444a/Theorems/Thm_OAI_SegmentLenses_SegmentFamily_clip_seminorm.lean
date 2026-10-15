-- Prove2me | Theorems.Thm_OAI_SegmentLenses_SegmentFamily_clip_seminorm
-- name    : OAI.SegmentLenses.SegmentFamily.clip_seminorm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:06:29.688158+00:00
-- url     : https://prove2.me/theorems/bd66f32f-0a89-4e2d-994b-4e46d8e7046c
-- title:
--   Clipping a segment family to an ancestral set preserves its seminorm on functions supported there
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and for a segment family $\mathcal F$ let $\|p\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}p(S)^2\big)^{1/2}$ be its family seminorm. A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$. For ancestral $H$ and a segment family $\mathcal F$, each set $S\cap H$ with $S\in\mathcal F$ is empty or a segment, and these sets are pairwise disjoint. The *clipped family* $\mathcal F\cap H$ is the segment family consisting of the nonempty sets among them.
--
--   Let $H\subseteq V$ be finite and ancestral, let $\mathcal F$ be a segment family, and let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$. Then
--   $$
--   \|p\|_{\mathcal F\cap H}=\|p\|_{\mathcal F}.
--   $$
--
--   So, when testing functions supported in a finite ancestral set, one may restrict to segment families whose members lie inside that set. This is used in the atomic description of the dual unit ball: the segment norm of a test supported in a finite ancestral set $K$ is already the supremum of its family seminorms over the segment families living inside $K$.
--
--   **Formalization Note** `F.clip hH` is `SegmentFamily.ofPieces` applied to the pieces `S ∩ H`, $S\in\mathcal F$. It takes the ancestrality proof `hH` as an argument, since ancestrality is what makes the pieces empty or segments. The support hypothesis is `p.support ⊆ H`. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/Pairing.lean#L330-L343

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem OAI.SegmentLenses.SegmentFamily.clip_seminorm {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    (F.clip hH).seminorm p = F.seminorm p := by sorry
