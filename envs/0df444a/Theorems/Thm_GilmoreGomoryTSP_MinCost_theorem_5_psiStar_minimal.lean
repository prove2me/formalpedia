-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_theorem_5_psiStar_minimal
-- name    : GilmoreGomoryTSP.MinCost.theorem_5_psiStar_minimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:44:50.288985+00:00
-- url     : https://prove2.me/theorems/ef2a83f3-8196-4435-ba64-b0a997ae5143
-- title:
--   Theorem 5 — the tour ψ* described in Theorem 3 is a minimal cost tour
-- statement:
--   Let $N=n+1$ jobs have starting states $A_i$ and final states $B_i$, numbered so that $j>i$ implies $B_j\ge B_i$. Let $f,g$ be locally integrable functions with $f(x)+g(x)\ge0$, and let $c_{ij}$ be the changeover costs (1) and $c(\psi)=\sum_i c_{i\psi(i)}$. Let $\varphi$ rank the $A$ ($j>i\Rightarrow A_{\varphi(j)}\ge A_{\varphi(i)}$), and let $\tau$ be a minimal cost spanning tree of $G_\varphi$ made of arcs $R_{q,q+1}$, where the arc $R_{q,q+1}$ costs $c_\varphi(\alpha_{q,q+1})=c(\varphi\alpha_{q,q+1})-c(\varphi)$. Let
--   $$\psi^*=\varphi\,\alpha_{i_1,i_1+1}\cdots\alpha_{i_l,i_l+1}\,\alpha_{j_1,j_1+1}\cdots\alpha_{j_m,j_m+1},$$
--   where $i_1>\dots>i_l$ are the arcs of $\tau$ whose lower node is of type 1 relative to $\varphi$ ($B_q\le A_{\varphi(q)}$) and $j_1<\dots<j_m$ those of type 2. Then $\psi^*$ is a tour, and
--   $$c(\psi^*)\le c(\psi)\quad\text{for every tour }\psi.$$
--
--   This is the paper's main result: the traveling salesman problem with the one state-variable costs (1) is solved exactly by an assignment, a minimum spanning tree over adjacent arcs, and interchanges executed in a prescribed order.
--
--   **Formalization Note** The minimum is over tours (single cycles through all jobs), not over all permutations. $\tau$ must be a spanning tree (minimal under inclusion) and of minimal cost among spanning trees made of adjacent arcs; by Lemma 2 that is also the minimum over all spanning trees. The execution order is that of the proof of Lemma 5 and of steps T2–T4 (p. 673); Theorem 3 as printed lists the indices in the opposite order, which on the paper's example (Tables I–III) gives a tour of cost 39 instead of Table III's optimal tour 1-2-7-4-5-6-3-1 of cost 34. "Any integrable functions" is read as local integrability on $\mathbb R$. For $N=1$ the identity is the only tour and the statement is trivially true.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 670, Theorem 5 (with ψ* as in Theorem 3, p. 665, in the execution order of Lemma 5, p. 664, and steps T2–T4, p. 673)

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem theorem_5_psiStar_minimal {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    IsTour (psiStar A B φ T) ∧
      ∀ ψ : Equiv.Perm (Fin (n + 1)), IsTour ψ →
        cost f g A B (psiStar A B φ T) ≤ cost f g A B ψ := by sorry

end GilmoreGomoryTSP.MinCost
