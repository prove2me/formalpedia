-- Prove2me | Theorems.Thm_OAI_Release075_reduced_path_or_cycle
-- name    : OAI.Release075.reduced_path_or_cycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:47:31.403773+00:00
-- url     : https://prove2.me/theorems/bb8fb3c2-1556-44d0-8f72-7c71c87d1654
-- title:
--   A reduced walk is a path or contains a short cycle
-- statement:
--   Let $p$ be a walk in a simple graph which is reduced, i.e. never returns to the vertex two steps back:
--   $$
--   p_n\ne p_{n+2}\quad\text{for all }n .
--   $$
--   Then either $p$ is a path (no repeated vertices), or the graph contains a cycle of length at most $\mathrm{length}(p)$.
--
--   No condition is imposed at the seam of a closed walk.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Presentation.lean#L32-L63

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation

open OAI OAI.Release075

theorem OAI.Release075.reduced_path_or_cycle {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : ReducedWalk p) :
    p.IsPath ∨ ∃ (c : V) (w : G.Walk c c), w.IsCycle ∧ w.length ≤ p.length := by sorry
