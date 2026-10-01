-- Prove2me | Theorems.Thm_HadwigerConj_exists_half_colorable_induced
-- name    : HadwigerConj.exists_half_colorable_induced
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T00:20:05.565152+00:00
-- url     : https://prove2.me/theorems/6ae9d6e7-72f7-4417-b677-01e47946ec92
-- title:
--   Theorem 4.2: no $K_{t+1}$ minor $\Rightarrow$ a $t$-colourable induced subgraph on half the vertices
-- statement:
--   Let $t\ge 0$ and let $G$ be a finite graph with no $K_{t+1}$ minor. Then there is a set $S$ of vertices with $|S|\ge |V(G)|/2$ such that the induced subgraph $G[S]$ is $t$-colourable.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Theorem 4.2 (p. 7)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem exists_half_colorable_induced (t : ℕ) {V : Type} [Finite V] (G : SimpleGraph V)
    (hG : ¬ HasCompleteMinor G (t + 1)) :
    ∃ S : Set V, Nat.card V ≤ 2 * S.ncard ∧ (G.induce S).Colorable t := by sorry
end HadwigerConj
