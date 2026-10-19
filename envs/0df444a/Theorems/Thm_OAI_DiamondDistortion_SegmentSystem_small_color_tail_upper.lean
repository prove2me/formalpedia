-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_small_color_tail_upper
-- name    : OAI.DiamondDistortion.SegmentSystem.small_color_tail_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:02:48.706607+00:00
-- url     : https://prove2.me/theorems/9928274a-791a-4621-b280-76aa10c7ca4c
-- title:
--   A bounded functional on a segment-norm space is uniformly small outside finitely many colour classes
-- statement:
--   Let $I$ be a set and let $\mathcal S$ be a collection of finite subsets of $I$, called *segments*, that contains every singleton $\{v\}$. A *test family* is a finite sequence $F=(S_1,\dots,S_n)$ ($n\ge0$) of pairwise disjoint segments. For a finitely supported function $p\colon I\to\mathbb{R}$ the *segment norm* is
--   $$\|p\|=\sup_{F}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   the supremum over all test families; it is finite (each term is at most $\sum_v|p(v)|$) and it is a norm, because singleton families give $|p(v)|\le\|p\|$. Let $J$ be the completion of the space of finitely supported functions under this norm and $J^*$ the space of continuous linear functionals on $J$ with the operator norm; a finitely supported $p$ is identified with its image in $J$, which has the same norm.
--
--   Let $K$ be a set of colours and $c\colon I\to K$ a colouring for which every segment is monochromatic: whenever $S$ is a segment and $u,v\in S$, then $c(u)=c(v)$.
--
--   **Theorem.** For every $x\in J^*$ and every $\varepsilon>0$ there is a finite set $C\subseteq K$ of colours such that every finitely supported $p\colon I\to\mathbb{R}$ with $c(v)\notin C$ for all $v$ with $p(v)\ne0$ satisfies
--   $$x(p)\le\varepsilon\,\|p\| .$$
--
--   Applying the statement to $-p$, which has the same support, gives the two-sided bound $|x(p)|\le\varepsilon\|p\|$. Thus, relative to the norm, a bounded functional carries only an arbitrarily small part of its mass outside finitely many colour classes. This is the first step in showing that functionals on the James-type space of a forest of bounded-height trees are approximated by their heads on finite sets, with the colour of a node being the tree containing it.
--
--   **Formalization Note** A segment system is a structure `T : SegmentSystem ι` with a predicate `IsSegment` on finite sets and the field `singleton`; test families are `T.Family`, indexed by `Fin n`, and the segment norm is `T.primalSeminorm`, the pointwise supremum of the family seminorms. Finitely supported functions are `ι →₀ ℝ`. The image of $p$ in $J$ is `T.finiteEmbedding p`, the space $J^*$ is `T.Dual`, and the monochromaticity of segments is the hypothesis `hsame`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean#L63-L129

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

theorem OAI.DiamondDistortion.SegmentSystem.small_color_tail_upper (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (x : T.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      x (T.finiteEmbedding p) ≤ ε*T.primalSeminorm p := by sorry
