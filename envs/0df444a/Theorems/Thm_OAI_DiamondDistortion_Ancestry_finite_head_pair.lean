-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_head_pair
-- name    : OAI.DiamondDistortion.Ancestry.finite_head_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:00:16.380206+00:00
-- url     : https://prove2.me/theorems/51d63832-4e3f-4181-896d-f535234dd84e
-- title:
--   Two terms of a bounded sequence of tree James dual functionals with almost equal finite heads
-- statement:
--   Let $(I,\le)$ be a partially ordered set in which the predecessors of every element form a chain: if $a\le c$ and $b\le c$, then $a\le b$ or $b\le a$. A *segment* is an order interval $[a,b]=\{v\in I: a\le v\le b\}$ with $a\le b$ that is a finite set. For a finitely supported function $p\colon I\to\mathbb{R}$ put
--   $$\|p\|=\sup_{S_1,\dots,S_n}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   where the supremum runs over all finite families $S_1,\dots,S_n$ ($n\ge0$) of pairwise disjoint segments. This is a norm on the space $c_{00}(I)$ of finitely supported real functions on $I$. Let $J$ be its completion and let $J^*$ be the space of continuous linear functionals on $J$, with the operator norm. For $v\in I$ let $e_v\in J$ be the indicator function of $\{v\}$, and let $e_v^*\in J^*$ be the coordinate functional, the continuous extension of $p\mapsto p(v)$. For a finite set $H\subseteq I$ the head and tail projections of $J^*$ are
--   $$P_Hx=\sum_{v\in H}x(e_v)\,e_v^*,\qquad Q_Hx=x-P_Hx\qquad(x\in J^*).$$
--   A set $H\subseteq I$ is *ancestral* if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$.
--
--   **Theorem.** Let $H\subseteq I$ be a finite ancestral set, let $(z_i)_{i\in\mathbb{N}}$ be a sequence in $J^*$ and let $R,\eta\in\mathbb{R}$ with $\|z_i\|\le R$ for all $i$ and $\eta>0$. Then there are indices $i\ne j$ such that
--   $$\Bigl\|P_H\Bigl(\tfrac12(z_i-z_j)\Bigr)\Bigr\|_{J^*}<\eta.$$
--
--   The head projection $P_H$ has finite-dimensional range, so a bounded sequence cannot keep its heads uniformly apart. The statement only produces one pair of distinct indices; it does not assert anything about a maximum over the infinitely many terms. In the separated-lens inequality it is used to find two members of a separated family whose half-difference lives almost entirely in the tail $Q_H$.
--
--   **Formalization Note** The order is an instance `A : Ancestry ι`, the segments form the system `A.segments` (built with `intervalSystem`), the norm on $c_{00}(I)$ is `A.segments.primalSeminorm`, $J$ is `A.segments.JamesSpace` (a `UniformSpace.Completion`), $J^*$ is `A.segments.Dual` (`StrongDual ℝ` of $J$), $e_v$ and $e_v^*$ are `unitVector v` and `coordinate v`, $P_H$ and $Q_H$ are `headDual H` and `tailDual H` for `H : Finset ι`, and ancestral sets are `A.Ancestral`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L1218-L1247

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

theorem OAI.DiamondDistortion.Ancestry.finite_head_pair {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (z : ℕ → A.segments.Dual) {R η : ℝ} (hz : ∀ i, ‖z i‖ ≤ R) (hη : 0 < η) :
    ∃ i j : ℕ, i ≠ j ∧ ‖A.segments.headDual H ((1/2:ℝ) • (z i-z j))‖ < η := by sorry
