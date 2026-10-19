-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_fields_eq_off_head
-- name    : OAI.RecursivePotentials.FiniteRootedTree.fields_eq_off_head
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:52:04.358877+00:00
-- url     : https://prove2.me/theorems/01743c58-d142-4474-b969-f0177b59a160
-- title:
--   Tree potentials outside an initial subtree depend only on the values outside it
-- statement:
--   Let $\iota$ be a finite set and let $T$ be a rooted tree on $\iota$, given by a root $r$, a parent map $\pi:\iota\to\iota$ with $\pi(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for every $s\neq r$. The children of a node $s$ are the nodes $c\neq r$ with $\pi(c)=s$. A set $H\subseteq\iota$ is *initial* if $r\in H$ and $\pi(s)\in H$ for every $s\in H$.
--
--   For $v:\iota\to\mathbb{R}$, the potential pair $\bigl(P_v(s),Q_v(s)\bigr)$ is defined by recursion from the deepest nodes towards the root:
--   $$P_v(s)=\max\bigl(A_v(s),\,v(s)+B_v(s)\bigr),\qquad Q_v(s)=\max\bigl(B_v(s),\,A_v(s)-v(s)\bigr),$$
--   where $A_v(s)=\bigl(\sum_{c}P_v(c)^2\bigr)^{1/2}$ and $B_v(s)=\bigl(\sum_{c}Q_v(c)^2\bigr)^{1/2}$, both sums running over the children $c$ of $s$ (an empty sum is $0$).
--
--   **Theorem.** Let $H\subseteq\iota$ be initial and let $v,w:\iota\to\mathbb{R}$ satisfy $v(s)=w(s)$ for every $s\notin H$. Then for every node $s\notin H$,
--   $$\bigl(P_v(s),\,Q_v(s)\bigr)=\bigl(P_w(s),\,Q_w(s)\bigr).$$
--
--   Thus the potentials at a node outside an initial set do not see the values of the vector inside that set. This locality is what makes the potentials of a vector vanishing outside $H$ equal to zero outside $H$, and what allows one to replace $x\pm z$ by $\pm z$ outside $H$ when $x$ vanishes off $H$; both facts enter the cubic convexity estimates for the tree norms $\|v\|=P_v(r)+Q_v(r)$ built from these potentials.
--
--   **Formalization Note** The pair $(P_v(s),Q_v(s))$ is `T.fields v s`, defined through `leastPair x a b = (max a (x + b), max b (-x + a))` with $a,b$ the `Real.sqrt` of the children sums; the tree is a `FiniteRootedTree ι` with `[Fintype ι]`, and $H$ is a `Finset ι` with `T.Initial H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean#L356-L370

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.FiniteRootedTree.fields_eq_off_head {H : Finset ι} (hH : T.Initial H) (v w : ι → ℝ)
    (hvw : ∀ s ∉ H, v s = w s) (s : ι) (hs : s ∉ H) :
    T.fields v s = T.fields w s := by sorry
