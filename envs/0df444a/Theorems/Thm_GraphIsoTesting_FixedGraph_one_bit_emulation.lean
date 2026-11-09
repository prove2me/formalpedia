-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_one_bit_emulation
-- name    : GraphIsoTesting.FixedGraph.one_bit_emulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:34.726439+00:00
-- url     : https://prove2.me/theorems/214c05f3-89bb-4c00-b393-f799514a6aed
-- title:
--   Claim 3.2 — One-bit emulation
-- statement:
--   Fix an exact $(3,6)$ matrix $A$. Each incidence query $z$ to the explicit degree-13 graph oracle has a coordinate $j(z)$ determined only by $A$ and $z$, or has no coordinate when its answer is constant. There is a concrete local answer function $F$ such that, for every $b$,
--
--   $$g_b(z)=\begin{cases}F(z,0),&j(z)\text{ absent},\\F(z,b_{j(z)}),&j(z)\text{ present}.\end{cases}$$
--
--   Thus at most one coordinate query to $b$ suffices to answer a graph query, including null and spoke answers. Vertex labels, the choice of inspected bit, and occurrence orderings are independent of the unknown right-hand side. This local simulation preserves the maximum query cap even for adaptive testers.
--
--   Differences from the source:
--   - generalization: the fixed matrix supplied by Lemma 2.3 in the section 3 preamble → every binary matrix with exact row weight three and column weight six; reason: the structural results use only the exact weights and distinct nonzero columns; the source matrices satisfy these conditions
--   - encoding: parity-dependent assignment labels and arbitrary fixed row orderings → b-independent even-assignment labels interpreted as α + bⱼ, with increasing row and occurrence orderings; reason: this is the fixed-label oracle convention of section 3.3 and a permitted choice of fixed orderings; graphs remain uncolored and all bijections are allowed
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 10, Claim 3.2 and equations (4)–(5); proof p. 11

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget

namespace GraphIsoTesting.FixedGraph

theorem one_bit_emulation {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (query : GadgetVertex m k × Fin 13) :
    ∀ b : Fin m → Bit, gadgetOracle A h b query =
      match queryCoordinate A h query with
      | none => emulateAnswer A h query 0
      | some j => emulateAnswer A h query (b j) := by sorry

end GraphIsoTesting.FixedGraph
