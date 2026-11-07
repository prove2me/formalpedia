-- Prove2me | Theorems.Thm_MISInducedMinor_lemma_3_1
-- name    : MISInducedMinor.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:43.880205+00:00
-- url     : https://prove2.me/theorems/b5989b43-c8c9-4993-970e-9ad8a5c4dba1
-- title:
--   Lemma 3.1 — $G$ and $G_F$ exclude the $5\times5$ grid as an induced minor
-- statement:
--   **Lemma 3.1.** The intermediate graph $G$ and hence $G_F$ exclude the $5\times5$ grid as an induced minor.
--
--   Precisely:
--
--   1. for all $R,C\in\mathbb N$, the $5\times5$ grid is not an induced minor of the intermediate graph with $R$ rows and $C$ columns;
--   2. for every graph $F$ on $n$ vertices, the $5\times5$ grid is not an induced minor of $G_F$.
--
--   This is the half of Theorem 1.5 that places the produced instances in the class.
--
--   Differences from the source:
--   - generalization: G with 2m rows and 2n − 1 columns → the intermediate graph with any numbers R of rows and C of columns; reason: the argument uses no property of these numbers; the paper's G is R = 2m, C = 2n − 1
--   - encoding: indices are 1-based: rows [2m], columns [2n − 1], vertex v_j in column 2j − 1 → 0-based: rows Fin (2m), columns Fin (2n − 1), vertex j − 1 : Fin n in column 2(j − 1); reason: Lean convention; the same graph up to the shift of indices, and Σ(j′ − j) is shift-invariant
--   - encoding: the vertices of F are ordered arbitrarily as v_1, …, v_n, and each edge e gets two reserved rows e_0, e_1 → F is a graph on Fin n with the order of Fin n, and edge number t of the lexicographic list of pairs a < b gets rows 2t (side 0) and 2t + 1 (side 1); reason: any vertex order is the order of Fin n after relabelling F, and the statement holds for every F; permuting rows is an automorphism of G, so the row assignment changes G_F only up to isomorphism
--   - encoding: H is an induced minor of G (obtained by removing vertices and contracting edges) → an induced-minor model of H in G exists: nonempty, pairwise disjoint branch sets, each inducing a connected subgraph, two distinct ones adjacent iff their vertices of H are; reason: the equivalent criterion stated on p.5
--   - encoding: the 5 × 5 grid (not defined in the paper) → pathGraph 5 □ pathGraph 5 on Fin 5 × Fin 5; reason: the standard grid graph
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), Lemma 3.1, p.7

import Definitions.Def_MISInducedMinor_GF
import Definitions.Def_MISInducedMinor_InducedMinorModel
import Definitions.Def_MISInducedMinor_grid5

set_option autoImplicit false

namespace MISInducedMinor

/-- **Lemma 3.1.** *The intermediate graph `G` and hence `G_F` exclude the 5 × 5 grid as an
induced minor.* arXiv:2609.11285 (sha256 e378b906…), Lemma 3.1, p.7.

**Formalization Note.** The first clause is for the intermediate graph with any numbers `R` of
rows and `C` of columns, the second for `G_F` of every graph `F` on `Fin n`. -/
theorem lemma_3_1 :
    (∀ R C : ℕ, ¬ IsInducedMinor grid5 (bonnetG R C)) ∧
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        ¬ IsInducedMinor grid5 (GF F) := by sorry

end MISInducedMinor
