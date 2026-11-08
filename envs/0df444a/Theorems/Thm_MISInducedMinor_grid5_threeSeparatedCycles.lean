-- Prove2me | Theorems.Thm_MISInducedMinor_grid5_threeSeparatedCycles
-- name    : MISInducedMinor.grid5_threeSeparatedCycles
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T07:20:16.079814+00:00
-- url     : https://prove2.me/theorems/58853210-e9b6-408c-81bf-ecd5702ca8a7
-- title:
--   Proof of Lemma 3.1, p.7, Figure 2 — the $5\times5$ grid has three separated cycles
-- statement:
--   The $5\times5$ grid has three vertex-disjoint, pairwise nonadjacent cycles $\Gamma_1,\Gamma_2,\Gamma_3$ such that, for any two of them, some path between them avoids the closed neighbourhood of the third.
--
--   The right side of Figure 2 (p.9) shows such cycles. Together with the next milestone it shows that the grid is not an induced minor of the intermediate graph $G$.
--
--   Differences from the source:
--   - encoding: the 5 × 5 grid (not defined in the paper) → pathGraph 5 □ pathGraph 5 on Fin 5 × Fin 5; reason: the standard grid graph
--   - encoding: a cycle of a graph and its vertices → a closed walk satisfying Mathlib's IsCycle (length at least 3, no repeated vertex except its ends) and its support; reason: Lean convention; the same cycles
--   - encoding: a path between two cycles → a walk; reason: every walk contains a path with the same ends whose vertices are among the walk's
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), proof of Lemma 3.1, p.7; Figure 2, p.9

import Definitions.Def_MISInducedMinor_grid5
import Definitions.Def_MISInducedMinor_ThreeSeparatedCycles

set_option autoImplicit false

namespace MISInducedMinor

/-- **The 5 × 5 grid has three vertex-disjoint and nonadjacent cycles such that there is a path
between any two of them avoiding the closed neighborhood of the third.** arXiv:2609.11285
(sha256 e378b906…), proof of Lemma 3.1, p.7, and Figure 2, p.9. -/
theorem grid5_threeSeparatedCycles : ThreeSeparatedCycles grid5 := by sorry

end MISInducedMinor
