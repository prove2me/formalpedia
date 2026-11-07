-- Prove2me | Theorems.Thm_MISInducedMinor_not_isInducedMinor_of_threeSeparatedCycles
-- name    : MISInducedMinor.not_isInducedMinor_of_threeSeparatedCycles
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:22.035225+00:00
-- url     : https://prove2.me/theorems/b8308f90-e7f0-4bd6-a5f1-ff83c1f2b8f3
-- title:
--   Proof of Lemma 3.1, p.7 — no graph with three separated cycles is an induced minor of $G$
-- statement:
--   Let $H$ be any graph with three vertex-disjoint, pairwise nonadjacent cycles $\Gamma_1,\Gamma_2,\Gamma_3$ such that there is a path between any two of them avoiding the closed neighbourhood of the third. Then, for all $R,C$, $H$ is not an induced minor of the intermediate graph $G$ with $R$ rows and $C$ columns.
--
--   With the previous milestone, this gives the first half of Lemma 3.1.
--
--   Differences from the source:
--   - generalization: G with 2m rows and 2n − 1 columns → the intermediate graph with any numbers R of rows and C of columns; reason: the argument uses no property of these numbers; the paper's G is R = 2m, C = 2n − 1
--   - encoding: H is an induced minor of G (obtained by removing vertices and contracting edges) → an induced-minor model of H in G exists: nonempty, pairwise disjoint branch sets, each inducing a connected subgraph, two distinct ones adjacent iff their vertices of H are; reason: the equivalent criterion stated on p.5
--   - encoding: a cycle of a graph and its vertices → a closed walk satisfying Mathlib's IsCycle (length at least 3, no repeated vertex except its ends) and its support; reason: Lean convention; the same cycles
--   - encoding: a path between two cycles → a walk; reason: every walk contains a path with the same ends whose vertices are among the walk's
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), proof of Lemma 3.1, p.7

import Definitions.Def_MISInducedMinor_bonnetG
import Definitions.Def_MISInducedMinor_InducedMinorModel
import Definitions.Def_MISInducedMinor_ThreeSeparatedCycles

set_option autoImplicit false

namespace MISInducedMinor

/-- **No graph `H` with three vertex-disjoint and nonadjacent cycles, any two joined by a path
avoiding the closed neighborhood of the third, is an induced minor of `G`.** arXiv:2609.11285
(sha256 e378b906…), proof of Lemma 3.1, p.7.

**Formalization Note.** `H` is any graph on any vertex type; `G` has any number `R` of rows and
`C` of columns. -/
theorem not_isInducedMinor_of_threeSeparatedCycles {W : Type*} (H : SimpleGraph W)
    (hH : ThreeSeparatedCycles H) (R C : ℕ) : ¬ IsInducedMinor H (bonnetG R C) := by sorry

end MISInducedMinor
