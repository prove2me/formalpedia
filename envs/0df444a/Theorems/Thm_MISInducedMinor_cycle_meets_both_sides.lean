-- Prove2me | Theorems.Thm_MISInducedMinor_cycle_meets_both_sides
-- name    : MISInducedMinor.cycle_meets_both_sides
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:43.019206+00:00
-- url     : https://prove2.me/theorems/dfc8d829-9023-4d09-af90-daafe4d5d104
-- title:
--   Proof of Lemma 3.1, p.7 — every cycle of $G$ uses both sides of some column
-- statement:
--   Let $G$ be the intermediate graph with $R$ rows and $C$ columns. Every cycle of $G$ contains two vertices in the same column but on different sides, that is, vertices of the form
--
--   $$(i,j,0)\quad\text{and}\quad(i',j,1).$$
--
--   Such vertices are adjacent in $G$, since each column is a complete bipartite graph between its sides. This is the first claim in the proof of Lemma 3.1: deleting the column bicliques leaves a forest.
--
--   Differences from the source:
--   - generalization: G with 2m rows and 2n − 1 columns → the intermediate graph with any numbers R of rows and C of columns; reason: the argument uses no property of these numbers; the paper's G is R = 2m, C = 2n − 1
--   - encoding: indices are 1-based: rows [2m], columns [2n − 1], vertex v_j in column 2j − 1 → 0-based: rows Fin (2m), columns Fin (2n − 1), vertex j − 1 : Fin n in column 2(j − 1); reason: Lean convention; the same graph up to the shift of indices, and Σ(j′ − j) is shift-invariant
--   - encoding: a cycle of a graph and its vertices → a closed walk satisfying Mathlib's IsCycle (length at least 3, no repeated vertex except its ends) and its support; reason: Lean convention; the same cycles
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), proof of Lemma 3.1, p.7

import Definitions.Def_MISInducedMinor_bonnetG

set_option autoImplicit false

namespace MISInducedMinor

/-- **Every cycle of `G` contains two adjacent vertices in the same column but on different
sides**, of the form `(i, j, 0)` and `(i′, j, 1)`. Bonnet, Chang, arXiv:2609.11285
(sha256 e378b906…), proof of Lemma 3.1, p.7.

**Formalization Note.** Stated for the intermediate graph with any number `R` of rows and `C` of
columns (the paper's `G` is `R = 2m`, `C = 2n − 1`). Two such vertices are adjacent in `G` by
definition. -/
theorem cycle_meets_both_sides (R C : ℕ) (v : Fin R × Fin C × Fin 2)
    (c : (bonnetG R C).Walk v v) (hc : c.IsCycle) :
    ∃ (i i' : Fin R) (j : Fin C), (i, j, 0) ∈ c.support ∧ (i', j, 1) ∈ c.support := by sorry

end MISInducedMinor
