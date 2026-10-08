-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_theorem_3_psiStar_tour_cost
-- name    : GilmoreGomoryTSP.MinCost.theorem_3_psiStar_tour_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:45:56.576987+00:00
-- url     : https://prove2.me/theorems/18a62904-604e-4889-91f9-1a48a7ad14ae
-- title:
--   Theorem 3 — ψ* is a tour with cost c(φ) + c_φ(τ)
-- statement:
--   Let $B$ be sorted, $f,g$ locally integrable with $f+g\ge0$, and $\varphi$ a permutation ranking the $A$. Let $\tau$ be a minimal cost spanning tree of $G_\varphi$ made of arcs $R_{q,q+1}$. Let $i_1>i_2>\dots>i_l$ be the lower indices of its type-1 arcs and $j_1<j_2<\dots<j_m$ those of its type-2 arcs (types relative to $\varphi$), and
--   $$\psi^*=\varphi\,\alpha_{i_1,i_1+1}\cdots\alpha_{i_l,i_l+1}\,\alpha_{j_1,j_1+1}\cdots\alpha_{j_m,j_m+1}.$$
--   Then $\psi^*$ is a tour with cost
--   $$c(\psi^*)=c(\varphi)+c_\varphi(\tau).$$
--
--   **Formalization Note** The page prints the type-1 indices increasing and the type-2 indices decreasing. Since $\psi\alpha$ means "apply $\alpha$ to $\psi$", that executes the interchanges in the reverse of the order of the proof of Lemma 5, which the proof of Theorem 3 says it follows, and of steps T2–T4 (p. 673). On the paper's own example (Tables I–III) the printed order gives a tour of cost 39, the corrected order gives Table III's tour 1-2-7-4-5-6-3-1 of cost 34. The statement uses the corrected order. The proof cites "Lemmas 2 and 4" for the cost; the cost statement is Lemma 5. "Minimal cost" is over spanning trees made of adjacent arcs, which by Lemma 2 have the same minimum cost as all spanning trees.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 665, Theorem 3 (execution order as in the proof of Lemma 5, p. 664, and steps T2–T4, p. 673)

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem theorem_3_psiStar_tour_cost {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    IsTour (psiStar A B φ T) ∧
      cost f g A B (psiStar A B φ T) = cost f g A B φ + adjTreeCost f g A B φ T := by sorry

end GilmoreGomoryTSP.MinCost
