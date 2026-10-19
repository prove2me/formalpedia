-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_defect_nonneg
-- name    : OAI.RecursivePotentials.FiniteRootedTree.defect_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:52:45.177208+00:00
-- url     : https://prove2.me/theorems/3c5c731f-fa27-4301-92db-9c3b34c48e75
-- title:
--   Midpoint convexity of tree potentials: the convexity defect is nonnegative
-- statement:
--   Let $\iota$ be a finite set and let $T$ be a rooted tree on $\iota$, given by a root $r$, a parent map $\pi:\iota\to\iota$ with $\pi(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for every $s\neq r$. The children of a node $s$ are the nodes $c\neq r$ with $\pi(c)=s$. A set $H\subseteq\iota$ is *initial* if $r\in H$ and $\pi(s)\in H$ for every $s\in H$.
--
--   For $v:\iota\to\mathbb{R}$, the potential pair $\bigl(P_v(s),Q_v(s)\bigr)$ is defined by recursion from the deepest nodes towards the root:
--   $$P_v(s)=\max\bigl(A_v(s),\,v(s)+B_v(s)\bigr),\qquad Q_v(s)=\max\bigl(B_v(s),\,A_v(s)-v(s)\bigr),$$
--   where $A_v(s)=\bigl(\sum_{c}P_v(c)^2\bigr)^{1/2}$ and $B_v(s)=\bigl(\sum_{c}Q_v(c)^2\bigr)^{1/2}$, both sums running over the children $c$ of $s$ (an empty sum is $0$). For $x,z:\iota\to\mathbb{R}$ and $s\in\iota$ define the convexity defect
--   $$\delta_{x,z}(s)=\frac{P_{x+z}(s)+P_{x-z}(s)}{2}-P_x(s).$$
--
--   **Theorem.** For all $x,z:\iota\to\mathbb{R}$ and every node $s\in\iota$ one has $\delta_{x,z}(s)\ge0$, that is,
--   $$P_x(s)\le\frac{P_{x+z}(s)+P_{x-z}(s)}{2}.$$
--
--   Since $P_u-Q_u=u$ for every $u$, the averaged second potential also satisfies $\tfrac12\bigl(Q_{x+z}(s)+Q_{x-z}(s)\bigr)=Q_x(s)+\delta_{x,z}(s)$, so the same nonnegative defect measures the convexity gain of both potentials. The defect is the local quantity that an energy argument propagates up the tree to obtain cubic lower bounds for $\tfrac12(\|x+z\|+\|x-z\|)-\|x\|$ in the tree norms $\|v\|=P_v(r)+Q_v(r)$.
--
--   **Formalization Note** The defect is `T.defect x z s`, defined as `((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2 - (T.fields x s).1`, where `T.fields v s` is the pair $(P_v(s),Q_v(s))$; the index type carries a `Fintype` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean#L404-L416

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.FiniteRootedTree.defect_nonneg (x z : ι → ℝ) (s : ι) : 0 ≤ T.defect x z s := by sorry
