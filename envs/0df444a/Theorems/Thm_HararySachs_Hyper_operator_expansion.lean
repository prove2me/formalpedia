-- Prove2me | Theorems.Thm_HararySachs_Hyper_operator_expansion
-- name    : HararySachs.Hyper.operator_expansion
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T03:24:57.353293+00:00
-- url     : https://prove2.me/theorems/7d9d10f3-51ed-4bce-8fad-cf7a3894434a
-- title:
--   Expansion of $\prod_i \hat f_i^{d_i}$ into rooted operators $\partial^{D_R}$
-- statement:
--   This is the expansion of a product of the paper's differential operators $\hat f_i$ into rooted operators. It states precisely the observation of Definitions 6–7 (pp. 7–8) that every addend of $\prod_i\hat f_i^{d_i}$ is the operator $\hat f_{D_R}$ of a rooting $R$.
--
--   Let $k\ge2$ and let $\mathcal H=([n],E)$ be a simple $k$-graph. Let $A=(A_{ij})$ be an $n\times n$ matrix of independent variables, and for a vertex $i$ let
--
--   $$
--   \hat f_i=\sum_{t_1,\ldots,t_{k-1}\in[n]} a_{i\,t_1\cdots t_{k-1}}\ \frac{\partial}{\partial A_{i t_1}}\cdots\frac{\partial}{\partial A_{i t_{k-1}}},
--   $$
--
--   where $a$ is the normalized adjacency hypermatrix, equal to $1/(k-1)!$ on orderings of edges. Fix an arrangement $(d_1,\ldots,d_n)$ of $d$ into nonnegative parts. Then, for every polynomial $P$ in the variables $A_{ij}$,
--
--   $$
--   \hat f_{n}^{\,d_n}\cdots\hat f_{1}^{\,d_1}\,P\;=\;\sum_{S}\ \sum_{R}\ \partial^{D_R}P.
--   $$
--
--   Here $S$ runs over the multisets of $d$ edges of $\mathcal H$, and $R$ runs over the rootings of $S$ in which exactly $d_v$ edges are rooted at $v$ for each vertex $v$. A rooting is a sequence $\bigl((v_1,e_1),\ldots,(v_d,e_d)\bigr)$ with $v_j\in e_j$, nondecreasing roots, and edge multiset $S$. The operator $\partial^{D_R}=\prod_{u\ne v}\partial^{m_R(u,v)}/\partial A_{uv}^{m_R(u,v)}$ differentiates once for every arc of the rooted digraph $D_R$, where $m_R(u,v)$ is the number of $j$ with $v_j=u$ and $v\in e_j$.
--
--   This identity converts the differential trace $\operatorname{Tr}_d(\mathcal H)$ of Equation (1) into a sum over rootings, which is the first step of the proof of Lemma 13.
--
--   **Formalization Note** The left-hand side is the mission's `applyAll`, which applies $\hat f_1^{d_1}$ first. The operators commute, so the order is immaterial. Arrangements are functions `Fin n → Fin (d+1)` with sum $d$. The rootings are the sequences `R : Fin S.card → Fin n × Finset (Fin n)` satisfying `IsRooting S R` together with the root-count condition, and $\partial^{D_R}$ is `diffMonomial (rootedArcs R)`. The identity is stated as an identity of polynomials, valid for every $P$.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, pp. 7-8, Definitions 6-7 and the remark that a rooted operator divides prod_i f_i^{d_i}; p. 12, proof of Lemma 13, display after 'Applying Lemma 10'

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_Veblen

namespace HararySachs.Hyper
open Classical

theorem operator_expansion {n k d : ℕ} (hk : 2 ≤ k)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (a : Fin n → Fin (d + 1)) (ha : (∑ i, (a i).val) = d) (P : AuxPoly n) :
    applyAll (k := k) E a P =
      ∑ S ∈ allMultisets E d,
        ∑ R : Fin S.card → Fin n × Finset (Fin n),
          if IsRooting S R ∧
              ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val
          then diffMonomial (rootedArcs R) P else 0 := by sorry

end HararySachs.Hyper
