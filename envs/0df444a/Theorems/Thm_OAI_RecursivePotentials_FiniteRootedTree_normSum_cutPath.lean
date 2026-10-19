-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_cutPath
-- name    : OAI.RecursivePotentials.FiniteRootedTree.normSum_cutPath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:09:18.743436+00:00
-- url     : https://prove2.me/theorems/9a285276-9c20-4d3c-a9ca-abd722d50a62
-- title:
--   Root-truncated path indicators have tree norm $2$
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$. For a node $s$, the *truncated path vector* is $\mathrm{cut}_s=\mathbf 1_{A(s)}-e_r$, the indicator function of $A(s)\setminus\{r\}$, where $e_r$ is the indicator of the root.
--
--   **Theorem.** For every node $s\neq r$,
--
--   $$\|\mathrm{cut}_s\|_T=2.$$
--
--   The truncated path vectors vanish at the root, and two consecutive ones differ by a basis vector at a non-root node. With this norm computation they provide uniformly bounded trees with separated increments in the joined tree space and its zero-root subspace, the input for excluding asymptotically uniformly convex renormings there.
--
--   **Formalization Note** $\mathrm{cut}_s$ is `T.cutPath s` $=$ `T.path s - Finsupp.single T.root 1`, where `T.path s` is the indicator of the ancestor set. The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean#L522-L542

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.FiniteRootedTree.normSum_cutPath (s : ι) (hs : s ≠ T.root) : T.normSum (T.cutPath s) = 2 := by sorry
