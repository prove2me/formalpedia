-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_separated_lens
-- name    : OAI.DiamondDistortion.Ancestry.separated_lens
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:00:50.973991+00:00
-- url     : https://prove2.me/theorems/6eac1d8a-31f7-43a7-b55d-2c3ab213f56a
-- title:
--   Quadratic separated-lens inequality for tree James dual functionals with finite head approximation
-- statement:
--   Let $(I,\le)$ be a partially ordered set in which the predecessors of every element form a chain: if $a\le c$ and $b\le c$, then $a\le b$ or $b\le a$. A *segment* is an order interval $[a,b]=\{v\in I: a\le v\le b\}$ with $a\le b$ that is a finite set. For a finitely supported function $p\colon I\to\mathbb{R}$ put
--   $$\|p\|=\sup_{S_1,\dots,S_n}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   where the supremum runs over all finite families $S_1,\dots,S_n$ ($n\ge0$) of pairwise disjoint segments. This is a norm on the space $c_{00}(I)$ of finitely supported real functions on $I$. Let $J$ be its completion and let $J^*$ be the space of continuous linear functionals on $J$, with the operator norm. For $v\in I$ let $e_v\in J$ be the indicator function of $\{v\}$, and let $e_v^*\in J^*$ be the coordinate functional, the continuous extension of $p\mapsto p(v)$. For a finite set $H\subseteq I$ the head and tail projections of $J^*$ are
--   $$P_Hx=\sum_{v\in H}x(e_v)\,e_v^*,\qquad Q_Hx=x-P_Hx\qquad(x\in J^*).$$
--   A set $H\subseteq I$ is *ancestral* if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$.
--
--   **Theorem.** Assume that every finite subset of $I$ is contained in a finite ancestral subset of $I$. Let $x\in J^*$ be approximable by finite heads: for every $\eta>0$ there is a finite ancestral $H\subseteq I$ with $\|Q_Hx\|<\eta$. Let $(z_i)_{i\in\mathbb{N}}$ be a sequence in $J^*$ and let $R\ge0$ and $\varepsilon>0$ be real numbers such that
--   - $\|x+z_i\|\le R$ and $\|x-z_i\|\le R$ for every $i$, and
--   - $\|z_i-z_j\|\ge\varepsilon$ for all $i\ne j$.
--
--   Then
--   $$\|x\|^2+\frac{\varepsilon^2}{16}\le R^2 .$$
--
--   Geometrically: if the ball of radius $R$ about the origin contains the two ends $x\pm z_i$ of infinitely many $\varepsilon$-separated chords through $x$, then the centre $x$ is shorter than $R$ by a definite quadratic amount. This is the "quadratic lens" property that drives the stage-by-stage distortion lower bound for the countably branching diamond graphs; it is applied to the full dual of the finite-height forest space and to the closed coordinate span over the tree of all finite words.
--
--   **Formalization Note** The order is an instance `A : Ancestry ι`, the segments form the system `A.segments` (built with `intervalSystem`), the norm on $c_{00}(I)$ is `A.segments.primalSeminorm`, $J$ is `A.segments.JamesSpace` (a `UniformSpace.Completion`), $J^*$ is `A.segments.Dual` (`StrongDual ℝ` of $J$), $e_v$ and $e_v^*$ are `unitVector v` and `coordinate v`, $P_H$ and $Q_H$ are `headDual H` and `tailDual H` for `H : Finset ι`, and ancestral sets are `A.Ancestral`. The hull assumption is the hypothesis `hfin` and the approximation assumption is `happrox`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L1264-L1328

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

theorem OAI.DiamondDistortion.Ancestry.separated_lens
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual}
    (happrox : ∀ η > 0, ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < η)
    (z : ℕ → A.segments.Dual) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hplus : ∀ i, ‖x+z i‖ ≤ R) (hminus : ∀ i, ‖x-z i‖ ≤ R)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) :
    ‖x‖^2+ε^2/16 ≤ R^2 := by sorry
