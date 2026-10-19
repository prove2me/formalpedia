-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_coordinate_predual_approximation
-- name    : OAI.DiamondDistortion.Ancestry.coordinate_predual_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:59:36.016598+00:00
-- url     : https://prove2.me/theorems/fb0ef86a-f21e-4fb1-b56a-e6367cd7004c
-- title:
--   Elements of the closed coordinate span of a tree James dual are approximated by finite ancestral heads
-- statement:
--   Let $(I,\le)$ be a partially ordered set in which the predecessors of every element form a chain: if $a\le c$ and $b\le c$, then $a\le b$ or $b\le a$. A *segment* is an order interval $[a,b]=\{v\in I: a\le v\le b\}$ with $a\le b$ that is a finite set. For a finitely supported function $p\colon I\to\mathbb{R}$ put
--   $$\|p\|=\sup_{S_1,\dots,S_n}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   where the supremum runs over all finite families $S_1,\dots,S_n$ ($n\ge0$) of pairwise disjoint segments. This is a norm on the space $c_{00}(I)$ of finitely supported real functions on $I$. Let $J$ be its completion and let $J^*$ be the space of continuous linear functionals on $J$, with the operator norm. For $v\in I$ let $e_v\in J$ be the indicator function of $\{v\}$, and let $e_v^*\in J^*$ be the coordinate functional, the continuous extension of $p\mapsto p(v)$. For a finite set $H\subseteq I$ the head and tail projections of $J^*$ are
--   $$P_Hx=\sum_{v\in H}x(e_v)\,e_v^*,\qquad Q_Hx=x-P_Hx\qquad(x\in J^*).$$
--   A set $H\subseteq I$ is *ancestral* if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$.
--
--   Let $\overline{\operatorname{span}}\{e_v^*:v\in I\}$ denote the norm closure in $J^*$ of the linear span of the coordinate functionals.
--
--   **Theorem.** Assume that every finite subset of $I$ is contained in a finite ancestral subset of $I$. Let $x\in\overline{\operatorname{span}}\{e_v^*:v\in I\}$ and $\varepsilon>0$. Then there is a finite ancestral set $H\subseteq I$ such that
--   $$\|Q_Hx\|_{J^*}=\Bigl\|x-\sum_{v\in H}x(e_v)\,e_v^*\Bigr\|_{J^*}<\varepsilon.$$
--
--   Thus every element of the closed coordinate span is a norm limit of its own heads $P_Hx$ over finite downward-closed sets. The hull assumption holds, for example, when every element of $I$ has only finitely many predecessors, as in the tree of all finite words over $\mathbb{N}$ ordered by the prefix relation. The result supplies the head-approximation hypothesis of the separated-lens inequality for the closed coordinate span over such a tree.
--
--   **Formalization Note** The order is an instance `A : Ancestry ι`, the segments form the system `A.segments` (built with `intervalSystem`), the norm on $c_{00}(I)$ is `A.segments.primalSeminorm`, $J$ is `A.segments.JamesSpace` (a `UniformSpace.Completion`), $J^*$ is `A.segments.Dual` (`StrongDual ℝ` of $J$), $e_v$ and $e_v^*$ are `unitVector v` and `coordinate v`, $P_H$ and $Q_H$ are `headDual H` and `tailDual H` for `H : Finset ι`, and ancestral sets are `A.Ancestral`. The closed span is `A.segments.CoordinatePredual`, the `topologicalClosure` of `Submodule.span ℝ (Set.range A.segments.coordinate)`, and the hull assumption is the hypothesis `hfin`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L1201-L1216

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

theorem OAI.DiamondDistortion.Ancestry.coordinate_predual_approximation
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual} (hx : x ∈ A.segments.CoordinatePredual)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < ε := by sorry
