-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_block_add_sq
-- name    : OAI.DiamondDistortion.SegmentSystem.block_add_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:02:12.827973+00:00
-- url     : https://prove2.me/theorems/3827776e-81be-4c5b-8794-4e8d5ae207e6
-- title:
--   Squared segment norms add over functions with disjoint colour supports
-- statement:
--   Let $I$ be a set and let $\mathcal S$ be a collection of finite subsets of $I$, called *segments*, that contains every singleton $\{v\}$. A *test family* is a finite sequence $F=(S_1,\dots,S_n)$ ($n\ge0$) of pairwise disjoint segments. For a finitely supported function $p\colon I\to\mathbb{R}$ the *segment norm* is
--   $$\|p\|=\sup_{F}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   the supremum over all test families; it is finite (each term is at most $\sum_v|p(v)|$) and it is a norm, because singleton families give $|p(v)|\le\|p\|$.
--
--   Let $K$ be a further set (of colours) and let $c\colon I\to K$ be a colouring for which every segment is monochromatic: whenever $S$ is a segment and $u,v\in S$, then $c(u)=c(v)$. For a finitely supported $p$ let $c(\operatorname{supp}p)=\{c(v):p(v)\ne0\}$ be its colour support.
--
--   **Theorem.** If $p,q\colon I\to\mathbb{R}$ are finitely supported and $c(\operatorname{supp}p)\cap c(\operatorname{supp}q)=\emptyset$, then
--   $$\|p+q\|^2\le\|p\|^2+\|q\|^2 .$$
--
--   So functions living on disjoint sets of colour classes behave, for the segment norm, like orthogonal vectors (an upper $\ell_2$ estimate across colour classes). This orthogonality is what allows a bounded functional to be shown small outside finitely many colour classes, for instance outside finitely many components of a forest.
--
--   **Formalization Note** A segment system is a structure `T : SegmentSystem ι` with a predicate `IsSegment` on finite sets and the field `singleton`; test families are `T.Family`, indexed by `Fin n`, and the segment norm is `T.primalSeminorm`, the pointwise supremum of the family seminorms. Finitely supported functions are `ι →₀ ℝ`. The colour support is `T.colorSupport c p`, the image of the `Finsupp` support under $c$, and the monochromaticity of segments is the hypothesis `hsame`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean#L34-L61

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

theorem OAI.DiamondDistortion.SegmentSystem.block_add_sq (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (p q : ι →₀ ℝ) (hd : Disjoint (T.colorSupport c p) (T.colorSupport c q)) :
    (T.primalSeminorm (p+q))^2 ≤ (T.primalSeminorm p)^2+(T.primalSeminorm q)^2 := by sorry
