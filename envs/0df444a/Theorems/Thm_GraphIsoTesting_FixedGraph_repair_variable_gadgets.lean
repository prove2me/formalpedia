-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_repair_variable_gadgets
-- name    : GraphIsoTesting.FixedGraph.repair_variable_gadgets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:38.05378+00:00
-- url     : https://prove2.me/theorems/6920b7db-8711-4ffe-9c40-853c3f7df99b
-- title:
--   Claim 3.5 — Recovering the variable gadgets
-- statement:
--   Fix an exact $(3,6)$ matrix $A$ and any vector $b$. For every role-preserving bijection $\mu:V(G_0)\to V(G_b)$ there is a variable-preserving bijection $\nu$ with
--
--   $$\Delta_b(\nu)\le(1+4d)\Delta_b(\mu),\qquad d=13.$$
--
--   The original role-preserving map can split variable gadgets. The resulting map sends each variable gadget onto another while allowing value flips, arbitrary variable permutations, and arbitrary behavior on constraint-gadget vertices. No stronger constraint-preservation predicate is used.
--
--   This is the second repair statement; its exact factor is again 53.
--
--   Differences from the source:
--   - generalization: the fixed matrix supplied by Lemma 2.3 in the section 3 preamble → every binary matrix with exact row weight three and column weight six; reason: the structural results use only the exact weights and distinct nonzero columns; the source matrices satisfy these conditions
--   - encoding: parity-dependent assignment labels and arbitrary fixed row orderings → b-independent even-assignment labels interpreted as α + bⱼ, with increasing row and occurrence orderings; reason: this is the fixed-label oracle convention of section 3.3 and a permitted choice of fixed orderings; graphs remain uncolored and all bijections are allowed
--   - encoding: d is the constructed graphs maximum degree bound → the factor is 1 + 4 * 13; reason: p. 9 supplies d = 13, with no extra degree hypothesis
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 13, Claim 3.5; proof pp. 13–14

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget

namespace GraphIsoTesting.FixedGraph

theorem repair_variable_gadgets {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) (μ : Equiv.Perm (GadgetVertex m k))
    (hμ : RolePreserving μ) :
    ∃ ν : Equiv.Perm (GadgetVertex m k), VariablePreserving ν ∧
      gadgetMismatch A h b ν ≤ (1 + 4 * 13) * gadgetMismatch A h b μ := by sorry

end GraphIsoTesting.FixedGraph
