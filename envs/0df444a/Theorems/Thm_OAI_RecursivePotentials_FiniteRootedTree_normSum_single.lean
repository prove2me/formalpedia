-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_single
-- name    : OAI.RecursivePotentials.FiniteRootedTree.normSum_single
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:07:33.575012+00:00
-- url     : https://prove2.me/theorems/400c9a84-1a3c-42c4-9649-4dcf01ccb088
-- title:
--   Basis vectors at non-root nodes have tree norm $2$
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$. For a node $c$, let $e_c$ be the function equal to $1$ at $c$ and $0$ elsewhere.
--
--   **Theorem.** For every node $c\neq r$,
--
--   $$\|e_c\|_T=2.$$
--
--   This exact value is used to show that consecutive path vectors in the tree spaces are uniformly separated: the difference of the path vectors of a node and of its parent is a basis vector, hence has norm $2$.
--
--   **Formalization Note** $e_c$ is `Finsupp.single c 1` and the tree norm is `T.normSum`. The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean#L503-L515

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.FiniteRootedTree.normSum_single (c : ι) (hc : c ≠ T.root) :
    T.normSum (Finsupp.single c 1) = 2 := by sorry
