-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_reach_bad_cross
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.reach_bad_cross
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:36:25.627683+00:00
-- url     : https://prove2.me/theorems/63f3e162-1202-49ad-9a27-b3324a03a720
-- title:
--   Neighbors with heavy overlap with the reach set carry little cross mass
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$ and neighborhoods $N(u)$, and let $w:V\to[0,\infty)$. Write $w(A)=\sum_{a\in A}w_a$, $e_w(A,B)=\sum_{a\in A}\sum_{b\in B,\,a\sim b}w_aw_b$, and
--
--   $$
--   \tau_w(v)=\sum_{u\in N(v)}w_u\,w\big(N(u)\cap N(v)\big)
--   $$
--
--   (twice the weighted triangle mass at $v$). For $y\in\mathbb R$ let $g_y(s)=s\,(y+\max\{0,\log(1/s)\})$ for $s>0$ and $g_y(0)=0$. The weight $w$ has the *cross-mass property with constant $C$* if $e_w(A,B)\le C\,g_y(w(A))$ for every real $y\ge1$ and all $A,B\subseteq V$ with $w(A)\le e^y$ and $w(B)\le e^y$.
--
--   *Reach sets.* For $\theta\in\mathbb R$ and $A\subseteq V$ let $\mathrm{enl}_\theta(A)=A\cup\{y\in V:\ w(A\cap N(y))\ge\theta\}$, and define $R^\theta_0(u)=N(u)$ and $R^\theta_{n+1}(u)=\mathrm{enl}_\theta\big(R^\theta_n(u)\big)$. For $x>0$ use the threshold $\theta(x)=1/(e^xx^6)$, and for $n\in\mathbb N$ and $v\in V$ define the *bad set*
--
--   $$
--   \mathrm{Bad}_n(v)=\big\{u\in N(v):\ w\big(R^{\theta(x)}_n(v)\cap N(u)\big)>x^8\big\}.
--   $$
--
--   Assume that $C\ge0$, that $w$ has the cross-mass property with constant $C$, that $x\ge32$, that $w(N(u))\le e^x$ for every vertex $u$, that $w(N(u)\cap N(v))\ge1/x$ for every edge $u\sim v$, and that $n\le2x$. Then for every vertex $v$,
--
--   $$
--   e_w\big(\mathrm{Bad}_n(v),\,N(v)\big)\le\frac{42C^2+2C}{x^4}\,\tau_w(v).
--   $$
--
--   So, when neighborhood masses are at most $e^x$ and every edge has common-neighborhood mass at least $1/x$, the neighbors of $v$ whose neighborhood meets the $n$-step reach set of $v$ in weight more than $x^8$ carry only an $O(C^2/x^4)$ fraction of the triangle mass at $v$. In the entropy analysis of the walk on oriented edges these exceptional neighbors can therefore be discarded at negligible cost.
--
--   **Formalization Note** The reach set is `reach G w (Numerical.threshold x) v n` with `Numerical.threshold x = 1 / (Real.exp x * x ^ 6)`; the bad set is `badSet G w S (x ^ 8) v` for `S u = reach G w (Numerical.threshold x) u n`; $\tau_w(v)$ is `triangleAt G w v`; the cross-mass property is `CrossBound G w C`; and $42C^2+2C$ is `exceptionalConstant C`. The hypothesis $n\le2x$ compares the natural number $n$, cast to a real number, with $2x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Reach.lean#L192-L216

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq

theorem OAI.CliqueFreeIndependence.WeightedGraph.reach_bad_cross (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) (v : V) :
    crossMass G w (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v)
      (neighbors G v) ≤ (exceptionalConstant C / x ^ 4) * triangleAt G w v := by sorry
