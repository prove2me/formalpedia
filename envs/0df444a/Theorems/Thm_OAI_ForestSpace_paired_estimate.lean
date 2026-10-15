-- Prove2me | Theorems.Thm_OAI_ForestSpace_paired_estimate
-- name    : OAI.ForestSpace.paired_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:21:11.222772+00:00
-- url     : https://prove2.me/theorems/cb66acde-ee53-4143-9001-9609aa1d7811
-- title:
--   Head–tail paired estimate for functionals on the segment-norm space $J(V)$
-- statement:
--   Let $(V,\le)$ be a partially ordered set. A *segment* of $V$ is a finite set $S\subseteq V$ that is a chain and is order-convex ($a,b\in S$ and $a\le c\le b$ imply $c\in S$). For a finitely supported function $u:V\to\mathbb{R}$ put
--
--   $$
--   \|u\|=\sup\Big\{\Big(\sum_{i=1}^m\Big(\sum_{v\in S_i}u(v)\Big)^2\Big)^{1/2}\ :\ S_1,\dots,S_m \text{ pairwise disjoint segments}\Big\},
--   $$
--
--   let $J(V)$ be the completion of the space of finitely supported functions under this norm, and let $J(V)^*$ be its full continuous dual with the operator norm. For $A\subseteq V$, a functional $x\in J(V)^*$ *annihilates* $A$ if $x(u)=0$ for every finitely supported $u$ that vanishes outside $A$.
--
--   Assume that $V$ is a forest order (if $a\le c$ and $b\le c$ then $a$ and $b$ are comparable) and that every element has finitely many predecessors (the set $\{w\in V: w\le v\}$ is finite for every $v\in V$). Let $H\subseteq V$ be a lower set ($w\le v$ and $v\in H$ imply $w\in H$), and let $x,y\in J(V)^*$ be such that $x$ annihilates $V\setminus H$ and $y$ annihilates $H$. Then
--
--   $$
--   \sqrt{\|x\|^2+\frac{\|y\|^2}{12}}\ \le\ \frac{\|x+y\|+\|x-y\|}{2}.
--   $$
--
--   In words: for a functional $x$ living on an ancestral head $H$ and a functional $y$ living on the complementary tail, the symmetric average $\tfrac12(\|x+y\|+\|x-y\|)$ is at least the weighted $\ell^2$-combination $\sqrt{\|x\|^2+\|y\|^2/12}$. This paired estimate is the main analytic input for the quantitative convexity of the dual space $J(T)^*$ of the finite-height forest $T$ in the main theorem: it yields the lower bound $\sqrt{1+t^2/12}-1$ for the averaged asymptotic midpoint modulus and the separated-midpoint (lens) inequality behind the diamond distortion bound.
--
--   **Formalization Note** `J V` is the uniform completion of the type `TestVector V` of finitely supported functions with the segment norm `rho`, and `FullDual V` is `StrongDual ℝ (J V)`. `Annihilates x A` only tests finitely supported vectors supported in `A` (embedded in the completion). The hypotheses are `ForestOrder V`, `∀ v, (Set.Iic v).Finite` and `IsLowerSet H` for `H : Set V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Polar.lean#L125-L156

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.paired_estimate (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (x y : FullDual V)
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H) :
    Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2 / 12) ≤ (‖x+y‖ + ‖x-y‖) / 2 := by sorry
