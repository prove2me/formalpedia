-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_sparse_multipliers_on
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.sparse_multipliers_on
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:29:05.709545+00:00
-- url     : https://prove2.me/theorems/c9c3bbaf-4fea-4096-ab74-83dd2bc4c49d
-- title:
--   Bounded random multipliers with mean $\mathbf 1_A$ and small expected edge mass on $K_{k+2}$-free sets
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, and let $w:V\to\mathbb R$ be a vertex weight with $w_v>0$ for every $v$. For $A\subseteq V$ write $w(A)=\sum_{v\in A}w_v$, and for $y:V\to\mathbb R$ let $E_G(y)=\sum_{\{u,v\}\in E(G)}y_uy_v$ be its edge mass (a sum over unordered edges). A *lottery of multipliers* is a finite list $L=((p_1,m_1),\dots,(p_N,m_N))$ of real weights $p_i$ and functions $m_i:V\to\mathbb R$; it is a *probability lottery* if $p_i\ge0$ for all $i$ and $\sum_ip_i=1$, and $\mathbb E_L[\Phi(m)]=\sum_ip_i\,\Phi(m_i)$ denotes the expectation of a real function $\Phi$ of the multiplier. For $k\in\mathbb N$ and $\varepsilon>0$ put
--
--   $$
--   b_k(\varepsilon)=\frac{2^{(k+2)k}}{\varepsilon^{k}} .
--   $$
--
--   Let $k\in\mathbb N$, let $A\subseteq V$ be a set that contains no clique of $G$ with $k+2$ vertices, and let $0<\varepsilon\le\frac12$. Then there is a probability lottery $L=((p_i,m_i))_{i\le N}$ such that:
--
--   1. every listed multiplier satisfies $0\le m_i(v)\le b_k(\varepsilon)$ for all $v\in V$, and $m_i(v)=0$ for all $v\notin A$;
--   2. the mean multiplier is the indicator of $A$: $\sum_ip_i\,m_i(v)=\mathbf 1_A(v)$ for every $v\in V$;
--   3. the reweighted vectors $w\odot m_i$, $(w\odot m_i)_v=w_v\,m_i(v)$, have small expected edge mass:
--
--   $$
--   \mathbb E_L\big[E_G(w\odot m)\big]=\sum_{i=1}^Np_i\,E_G(w\odot m_i)\le\varepsilon\,w(A)^2 .
--   $$
--
--   Thus the indicator of a $K_{k+2}$-free set is an average of bounded nonnegative multipliers supported on the set which, on average, remove almost all of the weighted edge mass inside $A$; the price is the bound $b_k(\varepsilon)$, polynomial of degree $k$ in $1/\varepsilon$. Such multiplier laws serve as test directions in the variational inequality for maximizers of the weighted potential $\sum_vq_v(1-\log q_v)-E_G(q)$, and lead to logarithmic cross-mass bounds for clique-free graphs.
--
--   **Formalization Note** The lottery has type `Law (V → ℝ)`, a `List (ℝ × (V → ℝ))`; outcomes need not be distinct, and the bound and support conditions (`BoundedOn L A (multiplierBound k ε)`) are imposed on every listed outcome regardless of its weight. The clique hypothesis is `G.CliqueFreeOn A (k+2)`; for $k=0$ it says that $A$ is an independent set. The expected edge mass is `expectedEdges G w L`, where `edgeMass` is defined as half of the sum over ordered adjacent pairs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/SparseMultipliers.lean#L40-L134

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.sparse_multipliers_on (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 < w v) (A : Finset V) (hfree : G.CliqueFreeOn (↑A) (k+2))
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ∃ L : Law (V → ℝ), IsProb L ∧ BoundedOn L A (multiplierBound k ε) ∧
      (∀ v, expect L (fun m ↦ m v) = if v ∈ A then 1 else 0) ∧
      expectedEdges G w L ≤ ε * (mass w A)^2 := by sorry
