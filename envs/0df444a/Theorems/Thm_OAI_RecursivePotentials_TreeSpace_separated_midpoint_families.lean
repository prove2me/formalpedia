-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_TreeSpace_separated_midpoint_families
-- name    : OAI.RecursivePotentials.TreeSpace.separated_midpoint_families
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:20:18.770409+00:00
-- url     : https://prove2.me/theorems/1795cfd0-1fef-46e6-aa20-1c5924fb6c92
-- title:
--   Midpoints of separated symmetric families lie uniformly inside the unit ball of a tree space
-- statement:
--   Let $T$ be a rooted tree on a node set $\iota$: there is a root $r\in\iota$, a parent map $\operatorname{par}:\iota\to\iota$ with $\operatorname{par}(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\operatorname{par}(s))<d(s)$ for every $s\neq r$ (the tree may be infinite and infinitely branching). A *child* of $s$ is a node $c\neq r$ with $\operatorname{par}(c)=s$; the *ancestor set* $A(s)$ consists of $s,\operatorname{par}(s),\operatorname{par}^2(s),\dots$ down to and including $r$. For a finitely supported $v:\iota\to\mathbb{R}$, let $H_v$ be the finite set formed by $r$ and the ancestor sets of all nodes in the support of $v$. The *potentials* $P_v,Q_v:\iota\to[0,\infty)$ vanish outside $H_v$ and are computed on $H_v$ from the leaves upward by $P_v(s)=\max\bigl(\alpha_s,\,v(s)+\beta_s\bigr)$ and $Q_v(s)=\max\bigl(\beta_s,\,-v(s)+\alpha_s\bigr)$, where $\alpha_s=\bigl(\sum_c P_v(c)^2\bigr)^{1/2}$ and $\beta_s=\bigl(\sum_c Q_v(c)^2\bigr)^{1/2}$, the sums running over the children $c$ of $s$ that lie in $H_v$. The *tree norm* of $v$ is $\|v\|_T=P_v(r)+Q_v(r)$. Let $X(T)$ be the completion of the space of finitely supported functions $\iota\to\mathbb{R}$ normed by $\|\cdot\|_T$.
--
--   For $M,\beta>0$ define the constant
--
--   $$\Gamma(M,\beta)=\frac{\beta\,\kappa}{8}\,e^{-K},\qquad \kappa=\frac{\beta^2}{2M^2},\quad \sigma=\frac{\beta\sqrt{\kappa}}{8},\quad K=\frac{4(2+\sqrt6)\bigl(1+\log(M/\sigma)\bigr)}{\kappa}.$$
--
--   **Theorem.** Let $0<\varepsilon\le2$, let $x\in X(T)$, and let $(z_n)_{n\in\mathbb{N}}$ be a sequence in $X(T)$ such that $\|x+z_n\|\le1$ and $\|x-z_n\|\le1$ for all $n$, and $\|z_i-z_j\|\ge\varepsilon$ for all $i\neq j$. Then
--
--   $$\|x\|\le1-\min\Bigl(\frac12,\ \Gamma\bigl(2,\tfrac{\varepsilon}{16}\bigr)\Bigr).$$
--
--   In words: a point which is the midpoint of infinitely many $\varepsilon$-separated symmetric pairs $x\pm z_n$ of the unit ball lies at distance at least $\min(\frac12,\Gamma(2,\varepsilon/16))>0$ inside the ball, uniformly in the tree. Applied to the joined tree it gives the separation property of the main statement, with $\eta=\min(\frac12,\Gamma(2,\varepsilon/16))$ for $\varepsilon\le2$.
--
--   **Formalization Note** $\Gamma(M,\beta)$ is `logarithmicGamma M β` (with `Real.log`, `Real.exp`, `Real.sqrt`); for $M=2$ and $\beta=\varepsilon/16\in(0,2]$ all quantities in its definition are positive, so no division-by-zero or logarithm conventions are involved. The tree $T$ is arbitrary (`TreeSpace T` for any `T : FiniteRootedTree ι`). The node type carries a decidable-equality instance (`DecidableEq`), used to form finitely supported functions; it is no mathematical restriction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean#L1179-L1244

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology
open UniformSpace
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem OAI.RecursivePotentials.TreeSpace.separated_midpoint_families {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2)
    (x : TreeSpace T) (z : ℕ → TreeSpace T)
    (hplus : ∀ n, ‖x+z n‖ ≤ 1) (hminus : ∀ n, ‖x-z n‖ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖z i - z j‖) :
    ‖x‖ ≤ 1 - min (1/2) (logarithmicGamma 2 (ε/16)) := by sorry
