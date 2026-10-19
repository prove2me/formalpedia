-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_path_step
-- name    : OAI.RecursivePotentials.FiniteRootedTree.path_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:04:45.592167+00:00
-- url     : https://prove2.me/theorems/68409ca6-9049-4edc-8fd6-84b5d8497804
-- title:
--   Consecutive path indicators in a rooted tree differ by one basis vector
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. The *path vector* $\mathrm{path}_s:\iota\to\mathbb{R}$ is the indicator function of $A(s)$, a finitely supported function, and $e_c$ denotes the function equal to $1$ at $c$ and $0$ elsewhere.
--
--   **Theorem.** For every node $c\neq r$,
--
--   $$\mathrm{path}_c=\mathrm{path}_{\operatorname{par}(c)}+e_c.$$
--
--   Moving one edge away from the root therefore adds exactly one basis vector to the path vector. Together with the norm computations for path vectors and basis vectors in the tree norm, this identity shows that the increments along branches of path vectors are basis vectors at sibling nodes, which is how bounded trees with separated, weakly null increments are built in the tree spaces.
--
--   **Formalization Note** `T.path s` is `extend (T.ancestors s) (fun _ => 1)`, an element of `ι →₀ ℝ`, and $e_c$ is `Finsupp.single c 1`. The ancestor set `T.ancestors s` is defined by recursion on the depth: it is $\{r\}$ when $s=r$ and $\{s\}\cup A(\operatorname{par}(s))$ otherwise. The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean#L354-L368

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.FiniteRootedTree.path_step (c : ι) (hc : c ≠ T.root) :
    T.path c = T.path (T.parent c) + Finsupp.single c 1 := by sorry
