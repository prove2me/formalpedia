-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_split_gain_le
-- name    : OAI.DiamondDistortion.Ancestry.split_gain_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:47:55.625565+00:00
-- url     : https://prove2.me/theorems/fc430328-5224-4335-b7e4-049b45dbd5f5
-- title:
--   Explicit squared gain from splitting disjoint segments at ancestral cuts
-- statement:
--   Let $(\iota,\le)$ be an *ancestral order*: a partially ordered set in which the predecessors of every element form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$ (as for the ancestry order of a rooted forest). A *segment* is a finite set $S\subseteq\iota$ that is an order interval $S=[a,b]=\{v\in\iota: a\le v\le b\}$ for some $a\le b$; in particular a segment is nonempty and $a=\min S$ is its least element. A set $H\subseteq\iota$ is *ancestral* (a head) if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$. For a finitely supported $u:\iota\to\mathbb{R}$, its segment norm $\|u\|$ is the supremum of $\big(\sum_{k=1}^n(\sum_{v\in S_k}u(v))^2\big)^{1/2}$ over all $n\in\mathbb{N}$ and all lists $S_1,\dots,S_n$ of pairwise disjoint segments.
--
--   Let $S_1,\dots,S_n$ be pairwise disjoint segments, let $H_1,\dots,H_n\subseteq\iota$ be ancestral sets, and let $u:\iota\to\mathbb{R}$ be finitely supported. Put $s_i=\sum_{v\in S_i}u(v)$ and let $t_i=\sum_{v\in S_i\setminus H_i}u(v)$ be the tail sum of $S_i$ outside $H_i$. Then
--   $$
--   \sum_{i=1}^n s_i^2+2\sum_{i=1}^n\big(t_i^2-s_i t_i\big)\le\|u\|^2 .
--   $$
--
--   The unsplit family alone gives $\sum_i s_i^2\le\|u\|^2$. The additional term $2\sum_i(t_i^2-s_it_i)=-2\sum_i t_i(s_i-t_i)$ is the explicit increase of the squared test obtained by splitting each segment at its head; its $i$-th summand is positive exactly when the tail sum $t_i$ and the head sum $s_i-t_i$ have opposite signs. Whenever this gain is large, $\sum_i s_i^2$ must be correspondingly smaller than $\|u\|^2$.
--
--   **Formalization Note** The segments form a represented family `F : A.segments.Family` with members `F.seg i` indexed by `Fin F.n`; the heads form a function `H` on the same index set, and the norm is `A.segments.primalSeminorm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L139-L160

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

theorem OAI.DiamondDistortion.Ancestry.split_gain_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, u v) ^ 2) +
      2 * (∑ i : Fin F.n, ((∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2 -
        (∑ v ∈ F.seg i, u v) * (∑ v ∈ (F.seg i).filter (· ∉ H i), u v))) ≤
        (A.segments.primalSeminorm u) ^ 2 := by sorry
