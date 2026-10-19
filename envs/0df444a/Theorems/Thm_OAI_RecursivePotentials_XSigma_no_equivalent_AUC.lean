-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_XSigma_no_equivalent_AUC
-- name    : OAI.RecursivePotentials.XSigma_no_equivalent_AUC
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:12:48.950979+00:00
-- url     : https://prove2.me/theorems/406ea61d-5b08-46be-85ac-810b16d563e3
-- title:
--   The sequence-tree space $X_\Sigma$ has no equivalent asymptotically uniformly convex norm
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$. Let $X(T)$ be the completion of the space of finitely supported functions $\iota\to\mathbb{R}$ normed by $\|\cdot\|_T$.
--
--   The *sequence tree* has as nodes all finite sequences of natural numbers; its root is the empty sequence, the parent of a nonempty sequence is obtained by deleting its last entry, and the depth is the length. Let $X_\Sigma=X(T_\Sigma)$ be the completion for the sequence tree $T_\Sigma$.
--
--   Let $E$ be a real normed space. An *equivalent norm* on $E$ is a seminorm $N$ together with constants $0<a\le b$ such that $a\|x\|\le N(x)\le b\|x\|$ for all $x\in E$. A *cofinite subspace* is a closed linear subspace $F\subseteq E$ such that $E/F$ is finite-dimensional. The (one-sided) *modulus of asymptotic uniform convexity* of $N$ is
--
--   $$\bar\delta_N(t)=\inf_{x\in E,\ N(x)=1}\ \sup_{F}\ \inf_{y\in F,\ N(y)=1}\bigl(N(x+ty)-1\bigr),$$
--
--   the supremum running over all cofinite subspaces $F$ of $E$. The norm $N$ is *asymptotically uniformly convex* (AUC) if $\bar\delta_N(t)>0$ for every $t>0$.
--
--   **Theorem.** No equivalent norm on $X_\Sigma$ is asymptotically uniformly convex: for every equivalent norm $N$ on $X_\Sigma$,
--
--   $$\neg\bigl(\forall t>0:\ \bar\delta_N(t)>0\bigr).$$
--
--   This is one of the claims of the main statement of the development, which also asserts that the averaged modulus of $X_\Sigma$ is positive at every radius; the space therefore separates the averaged convexity behaviour of its natural norm from asymptotic uniform convexity, which fails for every renorming.
--
--   **Formalization Note** $X_\Sigma$ is `XSigma` $=$ `TreeSpace sequenceTree` with node type `List ℕ`; equivalent norms are `EquivalentNorm XSigma` and the AUC property is `A.AUC`. `EquivalentNorm E` bundles the seminorm `N` with the constants `lower` $=a$ and `upper` $=b$; `A.modulus t` is defined with Lean's `sInf`/`sSup` on real sets (which return $0$ on empty or unbounded sets), but on an infinite-dimensional space and for $t\ge0$ all the sets involved are nonempty and bounded, so it is the genuine inf-sup-inf above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean#L459-L471

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

theorem OAI.RecursivePotentials.XSigma_no_equivalent_AUC (A : EquivalentNorm XSigma) : ¬A.AUC := by sorry
