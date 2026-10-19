-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_VariableExponent_finite_cubic
-- name    : OAI.RecursivePotentials.VariableExponent.finite_cubic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:21:22.172987+00:00
-- url     : https://prove2.me/theorems/3d64bda7-a815-453f-a333-9910de4e747f
-- title:
--   Cubic midpoint-gap inequality for the $(1+1/h)$-aggregated root-sum norm on a finite tree of height $h$
-- statement:
--   Let $I$ be a finite set carrying a rooted tree $T$: a root $r\in I$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth function $\operatorname{dep}:I\to\mathbb{N}$ with $\operatorname{dep}(r)=0$ and $\operatorname{dep}(\pi(s))<\operatorname{dep}(s)$ for every $s\neq r$. The children of a node $s$ are the nodes $c\neq r$ with $\pi(c)=s$, and $C(s)$ denotes their set. A subset $H\subseteq I$ is *initial* if $r\in H$ and $\pi(s)\in H$ for every $s\in H$.
--
--   Fix an exponent $p\ge1$. For a vector $v:I\to\mathbb{R}$ the *recursive potentials* $P_s(v),Q_s(v)\ge0$ are defined from the deepest nodes towards the root by
--   $$
--   P_s(v)=\max\bigl(A_s(v),\,v_s+B_s(v)\bigr),\qquad Q_s(v)=\max\bigl(B_s(v),\,A_s(v)-v_s\bigr),
--   $$
--   where $A_s(v)=\bigl(\sum_{c\in C(s)}P_c(v)^p\bigr)^{1/p}$ and $B_s(v)=\bigl(\sum_{c\in C(s)}Q_c(v)^p\bigr)^{1/p}$, empty sums being $0$; in particular $P_s(v)-Q_s(v)=v_s$ at every node. The *root sum* of $v$ is $\nu_p(v)=P_r(v)+Q_r(v)$, and $c_3=(6e)^{-3}$.
--
--   **Theorem.** Let $h\ge1$ be an integer and $p=1+\frac1h$. Assume that $\operatorname{dep}(c)=\operatorname{dep}(\pi(c))+1$ for every $c\neq r$ and that $\operatorname{dep}(s)\le h$ for every $s\in I$. Let $H\subseteq I$ be initial, and let $x,y:I\to\mathbb{R}$ satisfy $x_s=0$ for all $s\notin H$ and $y_s=0$ for all $s\in H$. Then
--   $$
--   c_3\,\nu_p(y)^3\;\le\;\Bigl(\frac{\nu_p(x+y)+\nu_p(x-y)}{2}-\nu_p(x)\Bigr)\,\max\bigl(\nu_p(x+y),\,\nu_p(x-y)\bigr)^2 .
--   $$
--
--   Here $x$ is carried by the finite "head" $H$ and $y$ by the complementary "tail", so the inequality is a uniform-convexity estimate of power type $3$ in tail directions: the midpoint gap $\frac12\bigl(\nu_p(x+y)+\nu_p(x-y)\bigr)-\nu_p(x)$, multiplied by $M^2$ where $M$ is the larger of $\nu_p(x+y)$ and $\nu_p(x-y)$, is at least $c_3\,\nu_p(y)^3$. The constant $c_3$ depends neither on the tree nor on $h$, although the exponent $p=1+1/h$ approaches $1$ as $h$ grows. This uniformity is what allows the estimate to be transported to finitely supported vectors on infinitely branching trees of height $h$, then to the completed spaces, and finally to an $\ell^2$-sum over all heights, where it yields cubic and sixth-power stability inequalities.
--
--   **Formalization Note** The tree is a `FiniteRootedTree ι` over an index type with `Fintype` and `DecidableEq` instances, and the exponent is a `ChildExponent` (a real number at least $1$) whose value is assumed to equal `heightExponent h`, that is $1+1/h$ for a positive natural number $h$. The potentials are `T.pfields p v`, computed with the aggregation $\bigl(\sum_{c}|f_c|^p\bigr)^{1/p}$ (the absolute values are harmless because potentials are nonnegative); $\nu_p$ is `T.pRootSum p` and $c_3$ is `cubicConstant`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableEstimates.lean#L969-L1013

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.VariableExponent
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology
variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)
variable {H : Finset ι} {x y : ι → ℝ} (hH : T.Initial H)
    (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)

theorem OAI.RecursivePotentials.VariableExponent.finite_cubic (h : ℕ+) (hp : p.val = heightExponent h)
    (hH : T.Initial H) (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val) :
    cubicConstant * T.pRootSum p y ^ 3 ≤
      ((T.pRootSum p (x+y) + T.pRootSum p (x-y)) / 2 - T.pRootSum p x) *
        max (T.pRootSum p (x+y)) (T.pRootSum p (x-y)) ^ 2 := by sorry
