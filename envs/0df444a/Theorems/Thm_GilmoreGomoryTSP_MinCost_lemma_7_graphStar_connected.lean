-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_lemma_7_graphStar_connected
-- name    : GilmoreGomoryTSP.MinCost.lemma_7_graphStar_connected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:01:50.312963+00:00
-- url     : https://prove2.me/theorems/7c3d6798-58f4-4822-953c-187f8d48956f
-- title:
--   Lemma 7 — if ψ is a tour, G_ψ* is connected
-- statement:
--   Let $\varphi$ and $\psi$ be permutations of the jobs and $G_\psi^*$ the graph consisting of the arcs of $G_\varphi$ together with every adjacent arc $R_{q,q+1}$ for which (22a) $i\le q<\varphi^{-1}\psi(i)$ holds for some $i$ or (22b) $\varphi^{-1}\psi(j)\le q<j$ holds for some $j$. If $\psi$ is a tour, then $G_\psi^*$ is connected.
--
--   Hence $G_\psi^*$ contains a spanning tree of $G_\varphi$ made of adjacent arcs, which is how the cost of a tour is compared with the cost of a minimal tree.
--
--   **Formalization Note** The statement involves only $\varphi$ and $\psi$, not the states or the costs; it is stated for an arbitrary permutation $\varphi$, which includes the paper's ranking permutation.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 668, Lemma 7

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate

namespace GilmoreGomoryTSP.MinCost

theorem lemma_7_graphStar_connected {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1)))
    (hψ : IsTour ψ) : (graphStar φ ψ).Connected := by sorry

end GilmoreGomoryTSP.MinCost
