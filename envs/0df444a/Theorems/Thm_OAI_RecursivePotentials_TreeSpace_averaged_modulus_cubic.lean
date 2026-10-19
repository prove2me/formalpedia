-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_TreeSpace_averaged_modulus_cubic
-- name    : OAI.RecursivePotentials.TreeSpace.averaged_modulus_cubic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:01:57.430336+00:00
-- url     : https://prove2.me/theorems/d078178a-85a4-4794-abba-7d3cee1d7ce8
-- title:
--   Cubic lower bound $t^3/128$ for the averaged modulus of completed tree spaces
-- statement:
--   Let $T$ be a rooted tree on an index set $\iota$ (which may be infinite): it has a root $r$, a parent map $\pi:\iota\to\iota$ with $\pi(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for every $s\neq r$. The children of $s$ are the nodes $c\neq r$ with $\pi(c)=s$, and a finite set $H\subseteq\iota$ is *initial* if $r\in H$ and $\pi(s)\in H$ for every $s\in H$.
--
--   For a finitely supported $v:\iota\to\mathbb{R}$ let $H_v$ be the finite initial set formed by the root, the points of the support of $v$ and all their ancestors. On the finite tree $H_v$ the potentials of $v$ are defined recursively from the deepest nodes towards the root by
--   $$P_v(s)=\max\bigl(A_v(s),\,v(s)+B_v(s)\bigr),\qquad Q_v(s)=\max\bigl(B_v(s),\,A_v(s)-v(s)\bigr),$$
--   with $A_v(s)=\bigl(\sum_cP_v(c)^2\bigr)^{1/2}$ and $B_v(s)=\bigl(\sum_cQ_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ in $H_v$; outside $H_v$ one puts $P_v=Q_v=0$. The finitely supported vectors with the norm $\|v\|=P_v(r)+Q_v(r)$ form a normed space $V_T$, and $X_T$ denotes its completion, in which $V_T$ is dense.
--
--   For a real normed space $E$, $x,y\in E$ and $t\in\mathbb{R}$ put
--   $$g(x,t,y)=\frac{\|x+ty\|+\|x-ty\|}{2}-1 .$$
--   A *cofinite subspace* of $E$ is a closed linear subspace $F$ such that the quotient $E/F$ is finite-dimensional. The averaged modulus of $E$ at $t$ is
--   $$\bar\delta_E(t)=\inf_{\|x\|=1}\ \sup_{F}\ \inf\bigl\{g(x,t,y):\ y\in F,\ \|y\|\ge1\bigr\},$$
--   where $F$ ranges over the cofinite subspaces of $E$.
--
--   **Theorem.** Assume that the index set $\iota$ is infinite. Then for every $t$ with $0<t<1$,
--   $$\frac{t^3}{128}\ \le\ \bar\delta_{X_T}(t).$$
--
--   The averaged modulus of every such completed tree space is therefore positive for $0<t<1$, with a power-type-three lower bound that does not depend on the tree. Applied to the sequence tree (all finite sequences of natural numbers, parent obtained by deleting the last entry) and to the joined tree (a common root to which, for every $h\ge1$, the tree of sequences of length at most $h$ is attached), it gives the bound $t^3/128$ for the averaged moduli of the corresponding spaces $X_\Sigma$ and $X_J$ in the main statement.
--
--   **Formalization Note** $V_T$ is `TreeVector T`, $X_T$ is `TreeSpace T = UniformSpace.Completion (TreeVector T)`, and $\bar\delta_{X_T}(t)$ is `averagedModulus (TreeSpace T) t`, defined with `sInf`/`sSup` on $\mathbb{R}$ over `CofiniteSubspace (TreeSpace T)`. Infiniteness of the index set is the instance `[Infinite ι]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean#L1289-L1313

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open UniformSpace
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.TreeSpace.averaged_modulus_cubic [Infinite ι] {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t ^ 3 / 128 ≤ averagedModulus (TreeSpace T) t := by sorry
