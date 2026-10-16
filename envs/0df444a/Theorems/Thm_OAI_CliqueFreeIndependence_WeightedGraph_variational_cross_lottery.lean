-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_variational_cross_lottery
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.variational_cross_lottery
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:25:56.74993+00:00
-- url     : https://prove2.me/theorems/12600e1f-cec5-4807-91e0-983728fbd680
-- title:
--   Variational cross-mass inequality at a potential maximizer, tested with a multiplier lottery
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$. For $y:V\to\mathbb R$ let $E_G(y)=\sum_{\{u,v\}\in E(G)}y_uy_v$ be its edge mass, and define the potential
--
--   $$
--   \Phi_G(q)=\sum_{v\in V}q_v\,(1-\log q_v)-E_G(q),\qquad q:V\to[0,\infty),
--   $$
--
--   with the convention $0\log0=0$. A weight $w:V\to\mathbb R$ is an *optimizer* if $w\ge0$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q\ge0$. For $A,B\subseteq V$ write $w(A)=\sum_{v\in A}w_v$ and $e_w(A,B)=\sum_{u\in A}\sum_{v\in B,\,u\sim v}w_uw_v$. A *probability lottery of multipliers* is a finite list $L=((p_i,m_i))_{i\le N}$ with $p_i\ge0$, $\sum_ip_i=1$ and $m_i:V\to\mathbb R$, and $\mathbb E_L[\Phi(m)]=\sum_ip_i\,\Phi(m_i)$; we write $(w\odot m)_v=w_v\,m(v)$.
--
--   Let $w$ be an optimizer, let $S,D\subseteq V$ be disjoint, let $b,\kappa,\varepsilon$ be real numbers with $\kappa\ge0$, and let $L$ be a probability lottery of multipliers such that
--
--   1. every listed multiplier satisfies $0\le m_i(v)\le b$ for all $v\in V$, and $m_i(v)=0$ for $v\notin S$;
--   2. $\sum_ip_i\,m_i(v)=\mathbf 1_S(v)$ for all $v\in V$;
--   3. $\mathbb E_L\big[E_G(w\odot m)\big]\le\varepsilon\,w(S)^2$.
--
--   Then
--
--   $$
--   \kappa\,e_w(S,D)\le\kappa^2\varepsilon\,w(S)^2+\frac{w(D)^2}{2}+w(D)+\kappa\,\log(1+\kappa b)\,w(S).
--   $$
--
--   This is the basic variational inequality behind the cross-mass bounds for optimizers: raising $w$ on $S$ in the random direction $\kappa\,(w\odot m)$ and deleting it on $D$ cannot increase the potential, and averaging over the lottery turns this into an upper bound for the weighted number of edges between $S$ and $D$. Taking $\kappa$ large and a lottery with small expected edge mass yields bounds of logarithmic type.
--
--   **Formalization Note** `IsOptimizer G w` asks for $w\ge0$ and global maximality of `potential G` among all nonnegative vectors; the logarithm is Mathlib's `Real.log` with `Real.log 0 = 0`, so the vertex term vanishes at $q_v=0$. The edge mass is `edgeMass`, half of the sum over ordered adjacent pairs; $e_w(S,D)$ is `crossMass G w S D`; the scaling parameter $\kappa$ is the Lean variable `k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/VariationalCross.lean#L97-L168

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery
universe u
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.variational_cross_lottery (G : SimpleGraph V) {w : V → ℝ} (hw : IsOptimizer G w)
    (S D : Finset V) (hSD : Disjoint S D) (L : Law (V → ℝ)) (hp : IsProb L)
    {b k ε : ℝ} (hk : 0 ≤ k) (hb : BoundedOn L S b)
    (hm : ∀ v, expect L (fun m ↦ m v) = if v ∈ S then 1 else 0)
    (he : expectedEdges G w L ≤ ε*(mass w S)^2) :
    k*crossMass G w S D ≤ k^2*ε*(mass w S)^2 + (mass w D)^2/2 + mass w D +
      k*Real.log (1+k*b)*mass w S := by sorry
