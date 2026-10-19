-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_crossing_cut_sum
-- name    : OAI.DiamondDistortion.Ancestry.crossing_cut_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:48:21.202029+00:00
-- url     : https://prove2.me/theorems/9319383c-802b-4ff1-8aff-7972578cb1e2
-- title:
--   Cutting at a later start point preserves the head sum of segments through a common exterior vertex
-- statement:
--   Let $(\iota,\le)$ be an *ancestral order*: a partially ordered set in which the predecessors of every element form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$ (as for the ancestry order of a rooted forest). A *segment* is a finite set $S\subseteq\iota$ that is an order interval $S=[a,b]=\{v\in\iota: a\le v\le b\}$ for some $a\le b$; in particular a segment is nonempty and $a=\min S$ is its least element. A set $H\subseteq\iota$ is *ancestral* (a head) if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$.
--
--   Let $H\subseteq\iota$ be an ancestral set and let $p:\iota\to\mathbb{R}$ be finitely supported with $p(v)=0$ for every $v\notin H$. Let $S$ be a member of a family of pairwise disjoint segments and $S'$ a member of a (possibly different) family of pairwise disjoint segments. Suppose there is a vertex $g\notin H$ with $g\in S$ and $g\in S'$, and that $\min S\le\min S'$. Then
--   $$
--   \sum_{v\in S,\ v\ge\min S'}p(v)=\sum_{v\in S'}p(v).
--   $$
--
--   Two segments through a common vertex outside the head agree on the head above the later starting point. Hence, for data supported in the head, cutting the segment that starts earlier at the starting point of the other one preserves exactly the other one's sum. This is used to compare segments of two different test families that meet at a common vertex outside a head.
--
--   **Formalization Note** The segments are `F.seg i` and `G.seg j` for represented families `F` and `G` of `A.segments`; $\min S$ is `A.first F i`, the lower endpoint chosen from the witness that `F.seg i` is an interval, which is its least element. The ancestral order is the class `Ancestry` and `A.Ancestral H` is downward closedness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L218-L252

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

theorem OAI.DiamondDistortion.Ancestry.crossing_cut_sum {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (i : Fin F.n) (j : Fin G.n) {g : ι} (hg : g ∉ H)
    (hgF : g ∈ F.seg i) (hgG : g ∈ G.seg j)
    (hfirst : A.first F i ≤ A.first G j) :
    (∑ v ∈ (F.seg i).filter (fun v => A.first G j ≤ v), p v) =
      ∑ v ∈ G.seg j, p v := by sorry
