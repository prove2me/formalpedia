-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_TreeSpace_finite_unit_dense
-- name    : OAI.RecursivePotentials.TreeSpace.finite_unit_dense
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:00:37.693298+00:00
-- url     : https://prove2.me/theorems/94de4799-91f4-4c44-94b3-f509094125d2
-- title:
--   Unit vectors of a completed tree space are limits of finitely supported unit vectors
-- statement:
--   Let $T$ be a rooted tree on an index set $\iota$ (which may be infinite): it has a root $r$, a parent map $\pi:\iota\to\iota$ with $\pi(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for every $s\neq r$. The children of $s$ are the nodes $c\neq r$ with $\pi(c)=s$, and a finite set $H\subseteq\iota$ is *initial* if $r\in H$ and $\pi(s)\in H$ for every $s\in H$.
--
--   For a finitely supported $v:\iota\to\mathbb{R}$ let $H_v$ be the finite initial set formed by the root, the points of the support of $v$ and all their ancestors. On the finite tree $H_v$ the potentials of $v$ are defined recursively from the deepest nodes towards the root by
--   $$P_v(s)=\max\bigl(A_v(s),\,v(s)+B_v(s)\bigr),\qquad Q_v(s)=\max\bigl(B_v(s),\,A_v(s)-v(s)\bigr),$$
--   with $A_v(s)=\bigl(\sum_cP_v(c)^2\bigr)^{1/2}$ and $B_v(s)=\bigl(\sum_cQ_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ in $H_v$; outside $H_v$ one puts $P_v=Q_v=0$. The finitely supported vectors with the norm $\|v\|=P_v(r)+Q_v(r)$ form a normed space $V_T$, and $X_T$ denotes its completion, in which $V_T$ is dense.
--
--   **Theorem.** Let $x\in X_T$ with $\|x\|=1$ and let $\varepsilon>0$. Then there is a finitely supported $v\in V_T$ with
--   $$\|v\|=1\qquad\text{and}\qquad\|v-x\|<\varepsilon .$$
--
--   No finiteness assumption on the tree is needed. The statement lets one test moduli of $X_T$ at unit vectors that are finitely supported, and every such vector is carried by the finite initial set formed by the root, its support and their ancestors.
--
--   **Formalization Note** $V_T$ is `TreeVector T` (finitely supported functions `ι →₀ ℝ` normed by `T.normSum`) and $X_T$ is `TreeSpace T = UniformSpace.Completion (TreeVector T)`; the distance $\|v-x\|$ is computed in the completion after coercing $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean#L1258-L1287

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open UniformSpace
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.TreeSpace.finite_unit_dense (x : TreeSpace T) (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : TreeVector T, ‖v‖ = 1 ∧ ‖(v : TreeSpace T) - x‖ < ε := by sorry
