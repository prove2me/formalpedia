-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_distance_transfer
-- name    : GraphIsoTesting.FixedGraph.distance_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:36.136786+00:00
-- url     : https://prove2.me/theorems/446ff774-1d64-49b0-900f-9e1438c57768
-- title:
--   Corollary 3.6 — Distance transfer
-- statement:
--   There is a uniform natural constant $K$, with the explicit witness
--
--   $$K=(1+4\cdot13)^2=2809,$$
--
--   such that for every exact $(3,6)$ binary matrix $A$, every vector $b$, and every unrestricted vertex bijection $\pi:V(G_0)\to V(G_b)$,
--
--   $$D_A(b)\le K\Delta_b(\pi).$$
--
--   The constant is chosen before the dimensions, matrix, vector, and bijection. In particular the inequality applies to a minimizing isomorphism alignment, giving the required distance transfer. It is not a minimum restricted to role-preserving or variable-preserving maps. The displayed value of $K$ is the one established in the source proof.
--
--   Differences from the source:
--   - generalization: the fixed matrix supplied by Lemma 2.3 in the section 3 preamble → every binary matrix with exact row weight three and column weight six; reason: the structural results use only the exact weights and distinct nonzero columns; the source matrices satisfy these conditions
--   - encoding: parity-dependent assignment labels and arbitrary fixed row orderings → b-independent even-assignment labels interpreted as α + bⱼ, with increasing row and occurrence orderings; reason: this is the fixed-label oracle convention of section 3.3 and a permitted choice of fixed orderings; graphs remain uncolored and all bijections are allowed
--   - encoding: there exists K, with proof witness (1+4d)² → a natural K with K = (1+4*13)² before all dimensions and data; reason: the source proof supplies this integral uniform witness and p. 9 supplies d = 13
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 14, Corollary 3.6 and its proof

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget

namespace GraphIsoTesting.FixedGraph

theorem distance_transfer :
    ∃ K : ℕ, K = (1 + 4 * 13)^2 ∧
      ∀ (m k : ℕ) (A : BinaryMatrix m k) (h : Sparse36 A)
        (b : Fin m → Bit) (π : Equiv.Perm (GadgetVertex m k)),
        imageDistance A b ≤ K * gadgetMismatch A h b π := by sorry

end GraphIsoTesting.FixedGraph
