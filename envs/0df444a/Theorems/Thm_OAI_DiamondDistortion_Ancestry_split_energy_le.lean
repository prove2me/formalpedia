-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_split_energy_le
-- name    : OAI.DiamondDistortion.Ancestry.split_energy_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:46:27.811718+00:00
-- url     : https://prove2.me/theorems/eb46914a-2717-49e9-9f4b-8399dfc9acf4
-- title:
--   Splitting disjoint segments at ancestral cuts stays within the squared segment norm
-- statement:
--   Let $(\iota,\le)$ be an *ancestral order*: a partially ordered set in which the predecessors of every element form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$ (as for the ancestry order of a rooted forest). A *segment* is a finite set $S\subseteq\iota$ that is an order interval $S=[a,b]=\{v\in\iota: a\le v\le b\}$ for some $a\le b$; in particular a segment is nonempty and $a=\min S$ is its least element. A set $H\subseteq\iota$ is *ancestral* (a head) if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$. For a finitely supported $u:\iota\to\mathbb{R}$, its segment norm $\|u\|$ is the supremum of $\big(\sum_{k=1}^n(\sum_{v\in S_k}u(v))^2\big)^{1/2}$ over all $n\in\mathbb{N}$ and all lists $S_1,\dots,S_n$ of pairwise disjoint segments.
--
--   Let $S_1,\dots,S_n$ be pairwise disjoint segments, let $H_1,\dots,H_n\subseteq\iota$ be ancestral sets (one for each segment), and let $u:\iota\to\mathbb{R}$ be finitely supported. Then
--   $$
--   \sum_{i=1}^n\bigg[\Big(\sum_{v\in S_i\cap H_i}u(v)\Big)^2+\Big(\sum_{v\in S_i\setminus H_i}u(v)\Big)^2\bigg]\le\|u\|^2 .
--   $$
--
--   Each segment is split simultaneously at its own head into a head part and a tail part, and the resulting $2n$ pieces are still tested against the same budget $\|u\|^2$. This simultaneous (rather than one-cut-at-a-time) splitting estimate is the basis of the explicit gain computation for cut segments.
--
--   **Formalization Note** The segments form a represented family `F : A.segments.Family` with members `F.seg i` indexed by `Fin F.n`; the heads form a function `H` on the same index set, and the norm is `A.segments.primalSeminorm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L100-L137

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

theorem OAI.DiamondDistortion.Ancestry.split_energy_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, ((∑ v ∈ (F.seg i).filter (· ∈ H i), u v) ^ 2 +
      (∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2)) ≤
      (A.segments.primalSeminorm u) ^ 2 := by sorry
