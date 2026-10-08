-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_theorem_2_tree_interchanges_tour
-- name    : GilmoreGomoryTSP.MinCost.theorem_2_tree_interchanges_tour
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:44:31.666003+00:00
-- url     : https://prove2.me/theorems/a3b8dc79-ba0c-498b-aa4e-e4ff5e9418b5
-- title:
--   Theorem 2 — the interchanges of a spanning tree of G_ψ, taken in any order, give a tour
-- statement:
--   Let $\psi$ be any permutation of the jobs and let $R_{i_1j_1},\dots,R_{i_{p-1}j_{p-1}}$ be the arcs of a spanning tree of $G_\psi$, i.e. a minimal set of additional arcs whose union with $G_\psi$ is connected. Then, for any order in which the arcs are listed,
--   $$\psi' = \psi\,\alpha_{i_1j_1}\alpha_{i_2j_2}\cdots\alpha_{i_{p-1}j_{p-1}}$$
--   is a tour.
--
--   This is the bridge from spanning trees of $G_\varphi$ to tours; it supplies the tour half of Theorem 3.
--
--   **Formalization Note** The arcs are given as a duplicate-free list $L$ of ordered pairs whose set is a spanning tree (`IsSpanningTree`), and the interchanges are executed left to right by folding $\sigma\mapsto\sigma\,\alpha_{e}$ over $L$ starting from $\psi$.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 661, Theorem 2

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem theorem_2_tree_interchanges_tour {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1)))
    (L : List (Fin (n + 1) × Fin (n + 1))) (hL : L.Nodup) (hT : IsSpanningTree ψ L.toFinset) :
    IsTour (L.foldl (fun σ e => σ * alpha e.1 e.2) ψ) := by sorry

end GilmoreGomoryTSP.MinCost
