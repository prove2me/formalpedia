-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_twice_coordinate_le_normSum
-- name    : OAI.RecursivePotentials.FiniteRootedTree.twice_coordinate_le_normSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:07:07.522676+00:00
-- url     : https://prove2.me/theorems/33a54b85-bdcd-44bd-a39f-470430a26001
-- title:
--   Coordinates of a tree vector vanishing at the root are at most half its tree norm
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$.
--
--   **Theorem.** Let $v:\iota\to\mathbb{R}$ be finitely supported with $v(r)=0$. Then for every node $s\in\iota$,
--
--   $$2\,|v(s)|\le\|v\|_T.$$
--
--   For general vectors one only has $|v(s)|\le\|v\|_T$; vanishing at the root improves this by a factor $2$. The bound supplies the lower estimates $\|e_c\|_T\ge2$ for the basis vector $e_c$ at a non-root node $c$ and $\|\mathbf 1_{A(s)\setminus\{r\}}\|_T\ge2$ for the root-truncated path vector of a non-root node $s$, and it shows that on vectors vanishing at the root every coordinate functional has norm at most $\tfrac12$.
--
--   **Formalization Note** The statement is about `T.normSum v` for `v : ι →₀ ℝ` with `v T.root = 0`. The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean#L487-L501

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.FiniteRootedTree.twice_coordinate_le_normSum (v : ι →₀ ℝ) (hv : v T.root = 0) (s : ι) :
    2 * |v s| ≤ T.normSum v := by sorry
