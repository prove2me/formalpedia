-- Prove2me | Theorems.Thm_KelsoCrawford_NoCore_example_efficient_assignments
-- name    : KelsoCrawford.NoCore.example_efficient_assignments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:36.632602+00:00
-- url     : https://prove2.me/theorems/f562409e-4e99-4c85-ae70-eb54f18c6b29
-- title:
--   Section 6, p. 1503 — in the example the maximal total product is 11½, attained exactly at j ← {1}, k ← {2, 3} and j ← {1, 2}, k ← {3}
-- statement:
--   In the market of the example of Section 6, every assignment $g$ of the three workers to the firms $j, k$ has total product at most $11\tfrac12$:
--   $$y^j\big(g^{-1}(j)\big) + y^k\big(g^{-1}(k)\big) \le 11\tfrac12,$$
--   and equality holds if and only if either $\{1\}$ is assigned to firm $j$ and $\{2, 3\}$ to firm $k$, or $\{1, 2\}$ is assigned to firm $j$ and $\{3\}$ to firm $k$.
--
--   Together with the efficiency of core allocations, this reduces the search for a core allocation of the example to these two assignments.
--
--   **Formalization Note** Workers $1, 2, 3$ are `0, 1, 2` and firms $j, k$ are `0, 1`; an assignment is any function from workers to firms (every worker is employed).
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1503, Section 6

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Notions
import Definitions.Def_KelsoCrawford_NoCore_Example

namespace KelsoCrawford.NoCore

theorem example_efficient_assignments :
    (∀ g : Fin 3 → Fin 2, noCoreMarket.totalProduct g ≤ 23 / 2) ∧
    (∀ g : Fin 3 → Fin 2, noCoreMarket.totalProduct g = 23 / 2 ↔
      (assignedTo g 0 = {0} ∧ assignedTo g 1 = {1, 2}) ∨
      (assignedTo g 0 = {0, 1} ∧ assignedTo g 1 = {2})) := by sorry

end KelsoCrawford.NoCore
