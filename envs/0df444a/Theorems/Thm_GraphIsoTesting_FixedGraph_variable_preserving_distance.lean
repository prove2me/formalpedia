-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_variable_preserving_distance
-- name    : GraphIsoTesting.FixedGraph.variable_preserving_distance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:41.802354+00:00
-- url     : https://prove2.me/theorems/8f13ee09-0418-4b36-a40e-7f80d58d905b
-- title:
--   Lemma 3.3 — Distance preservation under a variable-preserving bijection
-- statement:
--   Fix an exact $(3,6)$ binary matrix $A$ and any vector $b$. Every variable-preserving bijection $\nu:V(G_0)\to V(G_b)$ satisfies
--
--   $$D_A(b)\le\Delta_b(\nu).$$
--
--   A variable-preserving bijection may permute whole variable gadgets, flip each pair of values, and act arbitrarily on constraint-gadget vertices. No permutation must preserve the matrix or the constraint indices. Each unordered mismatch edge is counted once, and the coefficient is exactly 1.
--
--   This is the direct distance inequality used before repairing general bijections.
--
--   Differences from the source:
--   - generalization: the fixed matrix supplied by Lemma 2.3 in the section 3 preamble → every binary matrix with exact row weight three and column weight six; reason: the structural results use only the exact weights and distinct nonzero columns; the source matrices satisfy these conditions
--   - encoding: parity-dependent assignment labels and arbitrary fixed row orderings → b-independent even-assignment labels interpreted as α + bⱼ, with increasing row and occurrence orderings; reason: this is the fixed-label oracle convention of section 3.3 and a permitted choice of fixed orderings; graphs remain uncolored and all bijections are allowed
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 11, Lemma 3.3 and equation (6); proof pp. 11–12

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget

namespace GraphIsoTesting.FixedGraph

theorem variable_preserving_distance {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) (ν : Equiv.Perm (GadgetVertex m k))
    (hν : VariablePreserving ν) :
    imageDistance A b ≤ gadgetMismatch A h b ν := by sorry

end GraphIsoTesting.FixedGraph
