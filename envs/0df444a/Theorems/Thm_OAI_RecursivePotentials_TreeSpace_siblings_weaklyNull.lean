-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_TreeSpace_siblings_weaklyNull
-- name    : OAI.RecursivePotentials.TreeSpace.siblings_weaklyNull
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:11:48.88854+00:00
-- url     : https://prove2.me/theorems/d0551c62-1316-4b7d-8e1e-90f05d316214
-- title:
--   Basis vectors at distinct children of a node are weakly null in the tree space
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$. Let $X(T)$ be the completion of the space of finitely supported functions $\iota\to\mathbb{R}$ normed by $\|\cdot\|_T$. For a node $c$, let $b_c\in X(T)$ be the image of the function $e_c$ equal to $1$ at $c$ and $0$ elsewhere. A sequence $(x_k)$ in $X(T)$ is *weakly null* if $\varphi(x_k)\to0$ for every continuous linear functional $\varphi:X(T)\to\mathbb{R}$.
--
--   **Theorem.** Let $s\in\iota$ and let $f:\mathbb{N}\to\iota$ be injective with $f(k)$ a child of $s$ for every $k$ (that is, $f(k)\neq r$ and $\operatorname{par}(f(k))=s$). Then the sequence
--
--   $$\bigl(b_{f(k)}\bigr)_{k\in\mathbb{N}}\quad\text{is weakly null in }X(T).$$
--
--   Since each $b_{f(k)}$ has norm $2$, this is a seminormalized weakly null sequence; it provides the weakly null increments of the bounded trees of path vectors used to show that tree spaces admit no equivalent asymptotically uniformly convex norm.
--
--   **Formalization Note** $X(T)$ is `TreeSpace T`, the `UniformSpace.Completion` of `TreeVector T`; $b_c$ is `TreeSpace.basisVector T c`, and $f$ is an embedding `ℕ ↪ ι`. The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean#L387-L412

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
open UniformSpace

theorem OAI.RecursivePotentials.TreeSpace.siblings_weaklyNull (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) :
    WeaklyNull (fun k => basisVector T (f k)) := by sorry
