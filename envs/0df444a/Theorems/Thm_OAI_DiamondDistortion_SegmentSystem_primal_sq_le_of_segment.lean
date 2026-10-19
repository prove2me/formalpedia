-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_primal_sq_le_of_segment
-- name    : OAI.DiamondDistortion.SegmentSystem.primal_sq_le_of_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:03:24.323962+00:00
-- url     : https://prove2.me/theorems/5ccf64f4-feb8-4303-9811-b96b76a1bfa6
-- title:
--   Comparison of the segment norm with the $\ell_2$ norm from a per-segment estimate
-- statement:
--   Let $I$ be a set and let $\mathcal S$ be a collection of finite subsets of $I$, called *segments*, that contains every singleton $\{v\}$. A *test family* is a finite sequence $F=(S_1,\dots,S_n)$ ($n\ge0$) of pairwise disjoint segments. For a finitely supported function $p\colon I\to\mathbb{R}$ the *segment norm* is
--   $$\|p\|=\sup_{F}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   the supremum over all test families; it is finite (each term is at most $\sum_v|p(v)|$) and it is a norm, because singleton families give $|p(v)|\le\|p\|$.
--
--   **Theorem.** Let $p\colon I\to\mathbb{R}$ be finitely supported and let $L\ge0$. If every segment $S$ satisfies
--   $$\Bigl(\sum_{v\in S}p(v)\Bigr)^2\le L\sum_{v\in S}p(v)^2,$$
--   then
--   $$\|p\|^2\le L\sum_{v\in\operatorname{supp}p}p(v)^2 .$$
--
--   In words, a Cauchy–Schwarz-type estimate on each single segment, with a uniform constant $L$, upgrades to the comparison $\|p\|\le\sqrt L\,\|p\|_{\ell_2}$ with the $\ell_2$ norm. A typical use: if every segment meeting the support of $p$ has at most $L$ elements, then the hypothesis holds by the Cauchy–Schwarz inequality, so on trees of bounded height the segment norm is dominated by a multiple of the $\ell_2$ norm.
--
--   **Formalization Note** A segment system is a structure `T : SegmentSystem ι` with a predicate `IsSegment` on finite sets and the field `singleton`; test families are `T.Family`, indexed by `Fin n`, and the segment norm is `T.primalSeminorm`, the pointwise supremum of the family seminorms. Finitely supported functions are `ι →₀ ℝ`. The sum on the right runs over the `Finsupp` support `p.support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean#L170-L184

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
universe u v
open scoped BigOperators Classical Topology
open Set
variable {ι κ : Type*} (T : SegmentSystem ι)

theorem OAI.DiamondDistortion.SegmentSystem.primal_sq_le_of_segment (p : ι →₀ ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hS : ∀ S, T.IsSegment S → (∑ v ∈ S,p v)^2 ≤ L*(∑ v ∈ S,p v^2)) :
    (T.primalSeminorm p)^2 ≤ L*(∑ v ∈ p.support,p v^2) := by sorry
