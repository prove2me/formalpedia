-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_lemma_2_adjacent_min_tree
-- name    : GilmoreGomoryTSP.MinCost.lemma_2_adjacent_min_tree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:44:37.728604+00:00
-- url     : https://prove2.me/theorems/65e0ffe0-5b4c-4d83-b1ab-c7b1f4339ff5
-- title:
--   Lemma 2 — some minimal cost spanning tree of G_φ uses only arcs R_{i,i+1}
-- statement:
--   Let $B$ be sorted, $f,g$ locally integrable with $f+g\ge0$, and $\varphi$ a permutation ranking the $A$. Assign to each arc $R_{ij}$ the cost $c_\varphi(\alpha_{ij})$ and to a spanning tree $\tau$ of $G_\varphi$ the cost $c_\varphi(\tau)=\sum\{c_\varphi(\alpha_{ij})\mid R_{ij}\in\tau\}$. Then there is a minimal cost spanning tree for $G_\varphi$ that contains only arcs $R_{i,i+1}$: some spanning tree $T$ of $G_\varphi$ made of adjacent arcs satisfies
--   $$c_\varphi(T)\le c_\varphi(\tau)\quad\text{for every spanning tree } \tau \text{ of } G_\varphi.$$
--
--   Consequently the minimum cost over adjacent-arc trees, which is what the algorithm computes, equals the minimum over all spanning trees.
--
--   **Formalization Note** A general spanning tree is a finite set of ordered pairs $(i,j)$; minimality under inclusion rules out loops and repeated arcs.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 662, Lemma 2

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem lemma_2_adjacent_min_tree {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∃ T : Finset (Fin n), IsAdjTree φ T ∧
      ∀ E : Finset (Fin (n + 1) × Fin (n + 1)), IsSpanningTree φ E →
        adjTreeCost f g A B φ T ≤ arcSetCost f g A B φ E := by sorry

end GilmoreGomoryTSP.MinCost
