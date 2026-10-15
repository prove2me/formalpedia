-- Prove2me | Theorems.Thm_OAI_SegmentLenses_refinement_test_bound
-- name    : OAI.SegmentLenses.refinement_test_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:01:35.749894+00:00
-- url     : https://prove2.me/theorems/79b39f25-bea2-4f6b-b2e7-c68a602d1437
-- title:
--   Two disjoint segment pieces in each of disjoint blocks are controlled by the segment norm
-- statement:
--   Let $V$ be a set with a segment system, i.e. a class of finite subsets of $V$, called segments, that contains every singleton. A *segment family* is a finite set $\mathcal F$ of pairwise disjoint segments. For a finitely supported function $u:V\to\mathbb{R}$, the segment norm is
--   $$
--   \|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\Big(\sum_{S\in\mathcal F}\Big(\sum_{v\in S}u(v)\Big)^2\Big)^{1/2},
--   $$
--   the supremum over all segment families.
--
--   Let $\iota$ be a finite index set and let $(S_i)_{i\in\iota}$, $(A_i)_{i\in\iota}$, $(B_i)_{i\in\iota}$ be finite subsets of $V$ such that
--
--   - $S_i\cap S_j=\emptyset$ whenever $i\ne j$;
--   - $A_i\subseteq S_i$, $B_i\subseteq S_i$ and $A_i\cap B_i=\emptyset$ for every $i$;
--   - each $A_i$ and each $B_i$ is either empty or a segment.
--
--   Then for every finitely supported $u:V\to\mathbb{R}$,
--   $$
--   \sum_{i\in\iota}\Big[\Big(\sum_{v\in A_i}u(v)\Big)^2+\Big(\sum_{v\in B_i}u(v)\Big)^2\Big]\le\|u\|_{\mathrm{seg}}^2 .
--   $$
--
--   The blocks $S_i$ need not be segments themselves. They only serve as disjoint containers for the two pieces $A_i$ and $B_i$. The inequality lets one refine a disjoint family of blocks by splitting each block into two disjoint segment pieces, for instance the parts of an interval on either side of a cut point, and still compare the resulting sum of squares with the segment norm. This is the mechanism behind split-budget lower bounds for the segment norm.
--
--   **Formalization Note** $u$ is a `V →₀ ℝ` and $\|u\|_{\mathrm{seg}}$ is `segmentSeminorm V u`. Disjointness of the blocks is stated as `Pairwise fun i j => Disjoint (S i) (S j)`. The alternative "empty or a segment" appears because the segment predicate is not assumed to hold for the empty set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/Basic.lean#L239-L271

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset

theorem OAI.SegmentLenses.refinement_test_bound {V ι : Type*} [SegmentSystem V] [Fintype ι]
    (u : V →₀ ℝ) (S A B : ι → Finset V)
    (hd : Pairwise fun i j => Disjoint (S i) (S j))
    (hA : ∀ i, A i ⊆ S i) (hB : ∀ i, B i ⊆ S i)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hsA : ∀ i, A i = ∅ ∨ SegmentSystem.isSegment (A i))
    (hsB : ∀ i, B i = ∅ ∨ SegmentSystem.isSegment (B i)) :
    ∑ i, ((∑ v ∈ A i, u v) ^ 2 + (∑ v ∈ B i, u v) ^ 2) ≤
      segmentSeminorm V u ^ 2 := by sorry
