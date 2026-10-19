-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_siblings_le
-- name    : OAI.RecursivePotentials.FiniteRootedTree.normSum_siblings_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:05:34.373902+00:00
-- url     : https://prove2.me/theorems/5606509b-8f33-4be6-b808-d3c309361644
-- title:
--   Vectors supported on siblings have tree norm at most twice their $\ell^2$ norm
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$.
--
--   **Theorem.** Let $s\in\iota$ and let $v:\iota\to\mathbb{R}$ be finitely supported such that every node in the support of $v$ is a child of $s$ (that is, $c\neq r$ and $\operatorname{par}(c)=s$ whenever $v(c)\neq0$). Then
--
--   $$\|v\|_T\le2\Bigl(\sum_{c\in\operatorname{supp}v}v(c)^2\Bigr)^{1/2}.$$
--
--   So on vectors living on the children of a single node the tree norm is dominated by the Euclidean norm of the coefficients. This is the estimate behind the facts that a single basis vector at a non-root node has tree norm $2$ and that basis vectors at infinitely many distinct siblings form a weakly null sequence.
--
--   **Formalization Note** The tree norm is `T.normSum v` $=P_v(r)+Q_v(r)$ for `v : ι →₀ ℝ`, and the square root is `Real.sqrt`. The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean#L432-L485

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.FiniteRootedTree.normSum_siblings_le (s : ι) (v : ι →₀ ℝ)
    (hv : ∀ c ∈ v.support, c ≠ T.root ∧ T.parent c = s) :
    T.normSum v ≤ 2 * Real.sqrt (∑ c ∈ v.support, v c ^ 2) := by sorry
