-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_gadget_completeness
-- name    : GraphIsoTesting.FixedGraph.gadget_completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:33.496335+00:00
-- url     : https://prove2.me/theorems/cd4276fd-d36e-4f5a-bc45-8de89ba63015
-- title:
--   Lemma 3.1 — Completeness
-- statement:
--   Fix an exact $(3,6)$ binary matrix $A$ and a vector $b\in\mathbb F_2^m$. If the system $Ax=b$ is solvable, then the concrete parity graphs satisfy
--
--   $$G_b\cong G_0.$$
--
--   Here graph isomorphism is ordinary uncolored simple-graph isomorphism and may permute every vertex. This is the completeness half of the graph-testing reduction; it adds no index-rigidity requirement.
--
--   Differences from the source:
--   - generalization: the fixed matrix supplied by Lemma 2.3 in the section 3 preamble → every binary matrix with exact row weight three and column weight six; reason: the structural results use only the exact weights and distinct nonzero columns; the source matrices satisfy these conditions
--   - encoding: parity-dependent assignment labels and arbitrary fixed row orderings → b-independent even-assignment labels interpreted as α + bⱼ, with increasing row and occurrence orderings; reason: this is the fixed-label oracle convention of section 3.3 and a permitted choice of fixed orderings; graphs remain uncolored and all bijections are allowed
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 9, Lemma 3.1; proof pp. 9–10

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget

namespace GraphIsoTesting.FixedGraph

theorem gadget_completeness {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) (hb : b ∈ matrixImage A) :
    Nonempty (gadgetGraph A h b ≃g gadgetGraph A h 0) := by sorry

end GraphIsoTesting.FixedGraph
