-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_ZeroTreeSpace_finite_tail_dense
-- name    : OAI.RecursivePotentials.ZeroTreeSpace.finite_tail_dense
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:04:13.457344+00:00
-- url     : https://prove2.me/theorems/32bbe439-7afa-464d-b2dd-d2430b97bf98
-- title:
--   Tail elements of the zero-root tree space are limits of finitely supported tail vectors
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$.
--
--   Let $V_0(T)$ be the space of finitely supported $v:\iota\to\mathbb{R}$ with $v(r)=0$, normed by $\|v\|_0=P_v(r)$; since $P_v(r)-Q_v(r)=v(r)=0$, this equals $\tfrac12\|v\|_T$. Let $X_0(T)$ be the completion of $V_0(T)$, which contains $V_0(T)$ as a dense subspace. A finite set $H\subseteq\iota$ is *initial* if $r\in H$ and $\operatorname{par}(s)\in H$ for every $s\in H$. For such $H$ the head projection $\pi_H v=v\,\mathbf 1_H$ maps $V_0(T)$ into itself with operator norm at most $1$, and extends continuously to $\pi_H:X_0(T)\to X_0(T)$; the *tail* of $H$ is the kernel $\ker\pi_H\subseteq X_0(T)$.
--
--   **Theorem.** Let $H$ be a finite initial set, let $x\in X_0(T)$ satisfy $\pi_H x=0$, and let $\varepsilon>0$. Then there is a finitely supported $v\in V_0(T)$ such that
--
--   $$\pi_H v=0\quad(\text{that is, } v \text{ vanishes on } H)\qquad\text{and}\qquad \|v-x\|_{X_0(T)}<\varepsilon.$$
--
--   Thus the tail of an initial set is exactly the closure of the finitely supported vectors that vanish on the head. This approximation property is one of the completion statements for the zero-root space of the joined tree, and it lets estimates proved for finitely supported tail vectors pass to the whole tail by continuity.
--
--   **Formalization Note** `ZeroTreeVector T` is the kernel of the root coordinate on `TreeVector T` with the norm $P_v(r)$, `ZeroTreeSpace T` is its `UniformSpace.Completion`, and $\pi_H$ and the tail are `ZeroTreeVector.projection T H hH`, `ZeroTreeSpace.projection T H hH` and `ZeroTreeSpace.tail T H hH`, where `hH` is the proof that $H$ is initial. The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean#L218-L237

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.ZeroTreeSpace
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open UniformSpace
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.ZeroTreeSpace.finite_tail_dense (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T)
    (hx : x ∈ tail T H hH) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ZeroTreeVector T, ZeroTreeVector.projection T H hH v = 0 ∧
      ‖(v : ZeroTreeSpace T) - x‖ < ε := by sorry
