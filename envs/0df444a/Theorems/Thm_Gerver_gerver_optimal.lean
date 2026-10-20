-- Prove2me | Theorems.Thm_Gerver_gerver_optimal
-- name    : Gerver.gerver_optimal
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T20:15:44.16916+00:00
-- url     : https://prove2.me/theorems/5ce1553b-7887-474b-abf0-ffc7ebcaa0ae
-- title:
--   Gerver's sofa attains the maximum area of a moving sofa
-- statement:
--   The moving sofa problem is resolved: Gerver's sofa attains the maximum area of any moving sofa. Some sofa satisfying the Gerver construction — the monotone sofa of a rotation path carried by the five boundary curves solving Gerver's balancing ODEs — has area at least that of every shape that can be moved around the corner of the unit-width L-shaped hallway. This is Theorem 1.1.1 of the source, the mission's goal.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Theorem 1.1.1 (the main theorem)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Theorem 1.1.1 — the moving sofa problem: Gerver's sofa attains the maximum
area α_max of a moving sofa. Some sofa satisfying the Gerver construction —
the monotone sofa of a rotation path carried by the five boundary curves
solving Gerver's balancing ODEs — has area at least that of every moving
sofa. -/
theorem gerver_optimal :
    ∃ G, IsGerverSofa G ∧ ∀ S, IsMovingSofa S → area S ≤ area G := by
  sorry

end Gerver
