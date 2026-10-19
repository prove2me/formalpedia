-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_ZeroTreeSpace_tail_eq_coordinate_kernel
-- name    : OAI.RecursivePotentials.ZeroTreeSpace.tail_eq_coordinate_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:02:59.327351+00:00
-- url     : https://prove2.me/theorems/c0dbfbee-b797-4a8d-a759-7d4d944d0410
-- title:
--   In the zero-root tree space, the tail of an initial subtree is the common kernel of its coordinates
-- statement:
--   Let $T$ be a rooted tree on an index set $\iota$ (which may be infinite): it has a root $r$, a parent map $\pi:\iota\to\iota$ with $\pi(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for every $s\neq r$. The children of $s$ are the nodes $c\neq r$ with $\pi(c)=s$, and a finite set $H\subseteq\iota$ is *initial* if $r\in H$ and $\pi(s)\in H$ for every $s\in H$.
--
--   For a finitely supported $v:\iota\to\mathbb{R}$ let $H_v$ be the finite initial set formed by the root, the points of the support of $v$ and all their ancestors. On the finite tree $H_v$ the potentials of $v$ are defined recursively from the deepest nodes towards the root by
--   $$P_v(s)=\max\bigl(A_v(s),\,v(s)+B_v(s)\bigr),\qquad Q_v(s)=\max\bigl(B_v(s),\,A_v(s)-v(s)\bigr),$$
--   with $A_v(s)=\bigl(\sum_cP_v(c)^2\bigr)^{1/2}$ and $B_v(s)=\bigl(\sum_cQ_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ in $H_v$; outside $H_v$ one puts $P_v=Q_v=0$. The finitely supported vectors with the norm $\|v\|=P_v(r)+Q_v(r)$ form a normed space $V_T$, and $X_T$ denotes its completion, in which $V_T$ is dense.
--
--   The zero-root space is $V^0_T=\{v\in V_T:\ v(r)=0\}$ with the norm $\|v\|_0=P_v(r)$; since $P_v(r)-Q_v(r)=v(r)=0$, this is half of $\|v\|$. Let $X^0_T$ be its completion and $J:X^0_T\to X_T$ the continuous extension of the inclusion $V^0_T\subseteq V_T$. For $s\in\iota$ let $\ell_s:X_T\to\mathbb{R}$ be the continuous extension of $v\mapsto v(s)$, and define the coordinates of $x\in X^0_T$ by $x_s=\ell_s(Jx)$. For a finite initial set $H$, restriction $v\mapsto v\mathbf{1}_H$ maps $V^0_T$ into itself (because $r\in H$) without increasing $\|\cdot\|_0$; its continuous extension is the projection $\Pi^0_H$ on $X^0_T$, and the tail of $H$ is $\ker\Pi^0_H$. Finally, the head-coordinate map is
--   $$C_H:X^0_T\to\mathbb{R}^H,\qquad C_H(x)=(x_s)_{s\in H}.$$
--
--   **Theorem.** For every finite initial set $H$,
--   $$\ker\Pi^0_H=\ker C_H ,$$
--   that is, an element $x\in X^0_T$ satisfies $\Pi^0_Hx=0$ if and only if $x_s=0$ for every $s\in H$.
--
--   Since $C_H$ is a continuous linear map into the finite-dimensional space $\mathbb{R}^H$, it follows that the tail of $H$ is a closed subspace of codimension at most the number of elements of $H$. This is how the tails of the zero-root space are shown to be closed and finite-codimensional, one of the completion properties required of the space $X_0$ built on the joined tree.
--
--   **Formalization Note** $V^0_T$ is `ZeroTreeVector T`, the kernel of the root coordinate in `TreeVector T`, with norm `T.P (toTree T v) T.root`; $X^0_T$ is `ZeroTreeSpace T`, $J$ is `ZeroTreeSpace.inclusion T`, $\Pi^0_H$ is `ZeroTreeSpace.projection T H hH`, the tail is `ZeroTreeSpace.tail T H hH`, and $C_H$ is `ZeroTreeSpace.headCoordinates T H = (TreeSpace.headCoordinates T H).comp (inclusion T)`, with values in `H → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean#L196-L211

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

theorem OAI.RecursivePotentials.ZeroTreeSpace.tail_eq_coordinate_kernel (H : Finset ι) (hH : T.Initial H) :
    tail T H hH = (headCoordinates T H).ker := by sorry
