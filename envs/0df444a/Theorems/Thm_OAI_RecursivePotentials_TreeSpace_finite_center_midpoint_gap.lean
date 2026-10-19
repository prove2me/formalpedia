-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_TreeSpace_finite_center_midpoint_gap
-- name    : OAI.RecursivePotentials.TreeSpace.finite_center_midpoint_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:55:37.891964+00:00
-- url     : https://prove2.me/theorems/111bafc8-5551-4ae7-ab8a-1b4dc3d643ca
-- title:
--   Cubic midpoint gap $1+t^3/128$ for a unit head vector perturbed by a tail vector
-- statement:
--   Let $T$ be a rooted tree on an index set $\iota$ (which may be infinite): it has a root $r$, a parent map $\pi:\iota\to\iota$ with $\pi(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for every $s\neq r$. The children of $s$ are the nodes $c\neq r$ with $\pi(c)=s$, and a finite set $H\subseteq\iota$ is *initial* if $r\in H$ and $\pi(s)\in H$ for every $s\in H$.
--
--   For a finitely supported $v:\iota\to\mathbb{R}$ let $H_v$ be the finite initial set formed by the root, the points of the support of $v$ and all their ancestors. On the finite tree $H_v$ the potentials of $v$ are defined recursively from the deepest nodes towards the root by
--   $$P_v(s)=\max\bigl(A_v(s),\,v(s)+B_v(s)\bigr),\qquad Q_v(s)=\max\bigl(B_v(s),\,A_v(s)-v(s)\bigr),$$
--   with $A_v(s)=\bigl(\sum_cP_v(c)^2\bigr)^{1/2}$ and $B_v(s)=\bigl(\sum_cQ_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ in $H_v$; outside $H_v$ one puts $P_v=Q_v=0$. The finitely supported vectors with the norm $\|v\|=P_v(r)+Q_v(r)$ form a normed space $V_T$, and $X_T$ denotes its completion, in which $V_T$ is dense. For a finite initial set $H$, the restriction $v\mapsto v\mathbf{1}_H$ does not increase the norm of $V_T$; its continuous extension $\Pi_H:X_T\to X_T$ is a contractive projection, and the *tail* of $H$ is the closed subspace $\ker\Pi_H$.
--
--   **Theorem.** Let $H$ be a finite initial set, let $x\in V_T$ be finitely supported with support contained in $H$ and $\|x\|=1$, and let $z\in X_T$ satisfy $\Pi_Hz=0$. If $0<t<1$ and $\|z\|\ge t$, then
--   $$\frac{\|x+z\|+\|x-z\|}{2}\ \ge\ 1+\frac{t^3}{128}.$$
--
--   So a unit vector carried by a finite initial subtree gains at least $t^3/128$ on average when it is perturbed symmetrically by any tail vector of norm at least $t$. Combined with the approximation of unit vectors of $X_T$ by finitely supported ones, this uniform gain yields the lower bound $t^3/128$ for the averaged modulus of $X_T$ when the index set is infinite.
--
--   **Formalization Note** $V_T$ is `TreeVector T` (finitely supported functions `ι →₀ ℝ` normed by `T.normSum`, with $P_v,Q_v$ given by `T.P v`, `T.Q v`), $X_T$ is `TreeSpace T = UniformSpace.Completion (TreeVector T)`, $\Pi_H$ is `TreeSpace.projection T H hH` (the completion of `TreeVector.projection`, which is `Finsupp.filter (· ∈ H)`), and the tail is `TreeSpace.tail T H hH`. Finite initial sets are `Finset`s with `T.Initial H`. The vector $x$ is a `TreeVector T` whose underlying `Finsupp` has support contained in $H$, and it enters the norms through the coercion into the completion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean#L995-L1014

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open UniformSpace
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.TreeSpace.finite_center_midpoint_gap (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (hunit : ‖x‖ = 1) (z : TreeSpace T)
    (hz : z ∈ tail T H hH) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hzt : t ≤ ‖z‖) :
    1 + t ^ 3 / 128 ≤ (‖(x : TreeSpace T) + z‖ + ‖(x : TreeSpace T) - z‖) / 2 := by sorry
