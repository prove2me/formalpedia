-- Prove2me | Theorems.Thm_OAI_SegmentLenses_selected_split_budget
-- name    : OAI.SegmentLenses.selected_split_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:02:55.034919+00:00
-- url     : https://prove2.me/theorems/097f1bf4-811d-4d39-814c-3f32e65edd4f
-- title:
--   Split-gain budget: cuts in distinct disjoint intervals are paid for by the segment-norm slack
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let
--   $$
--   \|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\Big(\sum_{S\in\mathcal F}p(S)^2\Big)^{1/2}
--   $$
--   be the segment norm, the supremum taken over all segment families. Write $[a,c)=\{v\in V:\ a\le v<c\}$ for half-open intervals.
--
--   Let $\iota$ and $\Gamma$ be finite sets and let $p:V\to\mathbb{R}$ be finitely supported. Let $a,b:\iota\to V$ satisfy $a_i\le b_i$ for every $i$, and assume that the intervals $[a_i,b_i]$, $i\in\iota$, are pairwise disjoint. Let $s:\Gamma\to\iota$ be injective, let $\kappa:\Gamma\to V$ satisfy $a_{s(g)}\le\kappa(g)\le b_{s(g)}$ for every $g$, and let $\mathrm{cost}:\Gamma\to\mathbb{R}$ satisfy, for every $g\in\Gamma$, $\mathrm{cost}(g)\ge0$ and
--   $$
--   \mathrm{cost}(g)\le p\big([a_{s(g)},\kappa(g))\big)^2+p\big([\kappa(g),b_{s(g)}]\big)^2-p\big([a_{s(g)},b_{s(g)}]\big)^2 .
--   $$
--   Then
--   $$
--   \sum_{g\in\Gamma}\mathrm{cost}(g)\le\|p\|_{\mathrm{seg}}^2-\sum_{i\in\iota}p\big([a_i,b_i]\big)^2 .
--   $$
--
--   The map $s$ selects some of the intervals, each at most once, and $\kappa(g)$ is a cut point inside the selected interval. The right-hand side of the hypothesis is the gain in the sum of squares obtained by cutting $[a_{s(g)},b_{s(g)}]$ at $\kappa(g)$ into $[a_{s(g)},\kappa(g))$ and $[\kappa(g),b_{s(g)}]$. The right-hand side of the conclusion is the slack of the interval family, i.e. how far its sum of squares falls short of $\|p\|_{\mathrm{seg}}^2$. The theorem says that the gains of cuts in distinct intervals add up and are jointly bounded by this slack. It is the device used to charge opposite-sign crossings of two segment families to their slacks.
--
--   **Formalization Note** $p$ is a `V →₀ ℝ` and $\|p\|_{\mathrm{seg}}$ is `segmentSeminorm V p`. The intervals are `Finset.Ico` and `Finset.Icc`, and disjointness is `Pairwise` disjointness of the sets `Finset.Icc (a i) (b i)`. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean#L205-L271

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem OAI.SegmentLenses.selected_split_budget {ι Γ : Type*} [Fintype ι] [Fintype Γ]
    (p : V →₀ ℝ) (a b : ι → V) (hab : ∀ i, a i ≤ b i)
    (hd : Pairwise fun i j => Disjoint (Finset.Icc (a i) (b i)) (Finset.Icc (a j) (b j)))
    (select : Γ → ι) (hinj : Function.Injective select) (cut : Γ → V)
    (hcut : ∀ g, a (select g) ≤ cut g ∧ cut g ≤ b (select g))
    (cost : Γ → ℝ) (hcost : ∀ g, 0 ≤ cost g)
    (hgain : ∀ g, cost g ≤
      (∑ v ∈ Finset.Ico (a (select g)) (cut g), p v) ^ 2 +
      (∑ v ∈ Finset.Icc (cut g) (b (select g)), p v) ^ 2 -
      (∑ v ∈ Finset.Icc (a (select g)) (b (select g)), p v) ^ 2) :
    ∑ g, cost g ≤ segmentSeminorm V p ^ 2 -
      ∑ i, (∑ v ∈ Finset.Icc (a i) (b i), p v) ^ 2 := by sorry
