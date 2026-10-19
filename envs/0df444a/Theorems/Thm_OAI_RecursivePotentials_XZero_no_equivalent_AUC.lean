-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_XZero_no_equivalent_AUC
-- name    : OAI.RecursivePotentials.XZero_no_equivalent_AUC
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:14:57.035425+00:00
-- url     : https://prove2.me/theorems/be71d73b-a54b-4d2b-85e4-bfb615214e00
-- title:
--   The zero-root joined tree space $X_0$ has no equivalent asymptotically uniformly convex norm
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$.
--
--   The *joined tree* $T_J$ has a root $\varnothing$ and, for every integer $h\ge1$ and every finite sequence $s$ of natural numbers of length at most $h$, a node $(h,s)$. The parent of $(h,s)$ is the root when $s$ is empty and $(h,s')$ otherwise, where $s'$ is $s$ with its last entry deleted; the depth of $(h,s)$ is $|s|+1$. Thus $T_J$ joins, below a common root, complete infinitely branching trees of every finite height. Let $V_0$ be the space of finitely supported $v$ on $T_J$ with $v(\varnothing)=0$, normed by $\|v\|_0=P_v(\varnothing)$, which equals $\tfrac12\|v\|_{T_J}$ because $P_v(\varnothing)-Q_v(\varnothing)=v(\varnothing)=0$; let $X_0$ be its completion.
--
--   Let $E$ be a real normed space. An *equivalent norm* on $E$ is a seminorm $N$ together with constants $0<a\le b$ such that $a\|x\|\le N(x)\le b\|x\|$ for all $x\in E$. A *cofinite subspace* is a closed linear subspace $F\subseteq E$ such that $E/F$ is finite-dimensional. The (one-sided) *modulus of asymptotic uniform convexity* of $N$ is
--
--   $$\bar\delta_N(t)=\inf_{x\in E,\ N(x)=1}\ \sup_{F}\ \inf_{y\in F,\ N(y)=1}\bigl(N(x+ty)-1\bigr),$$
--
--   the supremum running over all cofinite subspaces $F$ of $E$. The norm $N$ is *asymptotically uniformly convex* (AUC) if $\bar\delta_N(t)>0$ for every $t>0$.
--
--   **Theorem.** No equivalent norm on $X_0$ is asymptotically uniformly convex: for every equivalent norm $N$ on $X_0$,
--
--   $$\neg\bigl(\forall t>0:\ \bar\delta_N(t)>0\bigr).$$
--
--   This is one of the claims of the main statement of the development, which also asserts that $X_0$ is reflexive and that its norm satisfies a cubic-type uniform convexity inequality for vectors supported on a head and perturbations vanishing there.
--
--   **Formalization Note** $X_0$ is `XZero` $=$ `ZeroTreeSpace joinedTree`, the `UniformSpace.Completion` of `ZeroTreeVector joinedTree` (the kernel of the root coordinate, normed by $P_v$ at the root). `EquivalentNorm E` bundles the seminorm `N` with the constants `lower` $=a$ and `upper` $=b$; `A.modulus t` is defined with Lean's `sInf`/`sSup` on real sets (which return $0$ on empty or unbounded sets), but on an infinite-dimensional space and for $t\ge0$ all the sets involved are nonempty and bounded, so it is the genuine inf-sup-inf above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean#L658-L669

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

open OAI OAI.RecursivePotentials
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology

theorem OAI.RecursivePotentials.XZero_no_equivalent_AUC (A : EquivalentNorm XZero) : ¬A.AUC := by sorry
