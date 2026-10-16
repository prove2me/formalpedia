-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_neighborhood_packing
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_packing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:28:36.980989+00:00
-- url     : https://prove2.me/theorems/22813c0f-e9ba-4c82-b611-4642feea83b8
-- title:
--   Greedy packing of dense neighbourhoods into an unbiased sparse multiplier lottery
-- statement:
--   **Setting.** Let $G$ be a simple graph on a finite vertex set $V$ and let $w:V\to\mathbb{R}$ satisfy $w_v>0$ for every $v$. Write $w(S)=\sum_{v\in S}w_v$ for $S\subseteq V$, $N(v)$ for the neighbourhood of $v$, and $E_G(x)=\sum_{\{u,u'\}\in E(G)}x_ux_{u'}$ for the edge mass of $x:V\to\mathbb{R}$. A *lottery* of multiplier vectors is a finite list $L=\bigl((p_1,m_1),\dots,(p_k,m_k)\bigr)$ of real weights $p_j$ and vectors $m_j:V\to\mathbb{R}$ (repetitions are allowed). For $f$ a real function of multiplier vectors write $\mathbb E_L[f(m)]=\sum_{j}p_j\,f(m_j)$, and let $|L|=\sum_jp_j$ be the total weight. The lottery is *nonnegative* if all $p_j\ge0$, and a *probability lottery* if moreover $|L|=1$. For $S\subseteq V$ and a real $\beta$, $L$ is *$\beta$-bounded on $S$* if every entry $m_j$, whatever its weight, satisfies $0\le m_j(u)\le\beta$ for all $u\in V$ and $m_j(u)=0$ for $u\notin S$. Given a simple graph $G$ on $V$ and weights $w:V\to\mathbb{R}$, the expected edge mass of $L$ is $\mathcal E_{G,w}(L)=\mathbb E_L\bigl[E_G(w\cdot m)\bigr]=\sum_jp_jE_G(w\cdot m_j)$, where $(w\cdot m)_u=w_u\,m(u)$ and $E_G(x)=\sum_{\{u,u'\}\in E(G)}x_ux_{u'}$ is the edge mass.
--
--   **Statement.** Let $A\subseteq V$ and let $s,\eta,b,B$ be real numbers with $s>0$, $\eta>0$, $b\ge0$, $B\ge2$, $(2/\eta)\,b\le B$ and $w(A)\le s$. Assume the following local hypothesis: for every $R\subseteq A$ and every $v\in R$ such that the set $D=R\cap N(v)$ satisfies $w(D)>\eta s$, there is a probability lottery $L$ that is $b$-bounded on $D$, has mean multiplier $\mathbb E_L[m(u)]=\mathbf 1[u\in D]$ for every $u\in V$, and satisfies $\mathcal E_{G,w}(L)\le\eta\,w(D)^2$. Then there exists a nonnegative lottery $L$ that is $B$-bounded on $A$, has mean multiplier $\mathbb E_L[m(u)]=\mathbf 1[u\in A]$ for every $u\in V$, and satisfies
--
--   $$
--   |L|\le\frac12+\frac{w(A)}{2s},\qquad \mathcal E_{G,w}(L)\le2\eta s\,w(A).
--   $$
--
--   In words: unbiased random multipliers with small expected edge mass, available on every dense neighbourhood, can be packed greedily into a single unbiased multiplier lottery on all of $A$, whose expected edge mass is linear rather than quadratic in $w(A)$; the multiplier bound grows from $b$ to $B$. The result is only a subprobability lottery (its total weight is at most $1$ because $w(A)\le s$); a zero outcome can then be added to obtain a probability lottery. This is the inductive step that builds sparse multipliers for clique-free graphs from multipliers on neighbourhoods, which are free of smaller cliques.
--
--   **Formalization Note** Lotteries are `Law (V → ℝ) = List (ℝ × (V → ℝ))`; the notions above are `expect`, `total`, `Positive`, `IsProb`, `BoundedOn` and `expectedEdges`. The mean multiplier at $u$ is `expect L (fun m ↦ m u)`. The hypothesis $w(A)\le s$ is part of the statement but is not used in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Packing.lean#L17-L128

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery
universe u
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_packing (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (A : Finset V) {s η b B : ℝ} (hs : 0 < s) (hη : 0 < η) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hbig : 2/η*b ≤ B) (_hAs : mass w A ≤ s)
    (hlocal : ∀ (R : Finset V), R ⊆ A → ∀ v ∈ R,
      η*s < mass w (R ∩ neighbors G v) →
      ∃ L : Law (V → ℝ), IsProb L ∧ BoundedOn L (R ∩ neighbors G v) b ∧
        (∀ u, expect L (fun m ↦ m u) = if u ∈ R ∩ neighbors G v then 1 else 0) ∧
        expectedEdges G w L ≤ η * (mass w (R ∩ neighbors G v))^2) :
    ∃ L : Law (V → ℝ), Positive L ∧ total L ≤ 1/2+mass w A/(2*s) ∧
      BoundedOn L A B ∧
      (∀ u, expect L (fun m ↦ m u) = if u ∈ A then 1 else 0) ∧
      expectedEdges G w L ≤ 2*η*s*mass w A := by sorry
