-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_normalize_subprob
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.normalize_subprob
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:19:57.458627+00:00
-- url     : https://prove2.me/theorems/aefc80cf-47eb-4d69-8007-f939c9f566e0
-- title:
--   Completing a subprobability lottery of multipliers to a probability lottery
-- statement:
--   Let $V$ be a finite set. A *lottery* of multiplier vectors is a finite list $L=\bigl((p_1,m_1),\dots,(p_k,m_k)\bigr)$ of real weights $p_j$ and vectors $m_j:V\to\mathbb{R}$ (repetitions are allowed). For $f$ a real function of multiplier vectors write $\mathbb E_L[f(m)]=\sum_{j}p_j\,f(m_j)$, and let $|L|=\sum_jp_j$ be the total weight. The lottery is *nonnegative* if all $p_j\ge0$, and a *probability lottery* if moreover $|L|=1$. For $S\subseteq V$ and a real $\beta$, $L$ is *$\beta$-bounded on $S$* if every entry $m_j$, whatever its weight, satisfies $0\le m_j(u)\le\beta$ for all $u\in V$ and $m_j(u)=0$ for $u\notin S$. Given a simple graph $G$ on $V$ and weights $w:V\to\mathbb{R}$, the expected edge mass of $L$ is $\mathcal E_{G,w}(L)=\mathbb E_L\bigl[E_G(w\cdot m)\bigr]=\sum_jp_jE_G(w\cdot m_j)$, where $(w\cdot m)_u=w_u\,m(u)$ and $E_G(x)=\sum_{\{u,u'\}\in E(G)}x_ux_{u'}$ is the edge mass.
--
--   Let $G$ be a simple graph on $V$, let $w:V\to\mathbb{R}$ be arbitrary, let $A\subseteq V$ and $b\ge0$, and let $L$ be a nonnegative lottery with $|L|\le1$ that is $b$-bounded on $A$. Then there exists a probability lottery $K$, also $b$-bounded on $A$, such that
--
--   $$
--   \mathbb E_K[m(v)]=\mathbb E_L[m(v)]\quad\text{for all }v\in V,\qquad \mathcal E_{G,w}(K)=\mathcal E_{G,w}(L).
--   $$
--
--   Thus a subprobability lottery of bounded multipliers can be completed to a genuine probability distribution without changing the mean multiplier at any vertex or the expected edge mass. This allows constructions to work with subprobability lotteries (for example, those produced by greedy packing) and normalize only at the very end.
--
--   **Formalization Note** Lotteries are `Law (V → ℝ) = List (ℝ × (V → ℝ))`; the notions above are `expect`, `total`, `Positive`, `IsProb`, `BoundedOn` and `expectedEdges`. The mean multiplier at $u$ is `expect L (fun m ↦ m u)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean#L118-L137

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u
open Lottery
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.normalize_subprob (G : SimpleGraph V) (w : V → ℝ) {L : Law (V → ℝ)}
    (hL : Positive L) (hsum : total L ≤ 1) {A : Finset V} {b : ℝ} (hb : 0 ≤ b)
    (hbL : BoundedOn L A b) :
    ∃ K : Law (V → ℝ), IsProb K ∧ BoundedOn K A b ∧
      (∀ v, expect K (fun m ↦ m v) = expect L (fun m ↦ m v)) ∧
      expectedEdges G w K = expectedEdges G w L := by sorry
