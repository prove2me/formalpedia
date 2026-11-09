-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_gadget_interface
-- name    : GraphIsoTesting.FixedGraph.gadget_interface
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:26.513448+00:00
-- url     : https://prove2.me/theorems/457bfcb9-7bc3-44e1-a9ff-c31f401eb70d
-- title:
--   Sections 3.1–3.3 — Gadget size, degrees, and oracle validity
-- statement:
--   For every exact $(3,6)$ binary matrix $A$ and every right-hand side $b$, the explicitly constructed graph and oracle satisfy
--
--   $$|V(G_b)|=3k+5m,\qquad\Delta(G_b)\le13.$$
--
--   Variable anchors have degree 2, values degree 13, and both constraint anchors and assignments degree 4. The explicit incidence oracle is valid: it enumerates every distinct neighbor once in an initial segment and returns null afterwards.
--
--   This unnumbered interface obligation records the size and degree facts on p. 9 and checks that the formulas on p. 10 describe the actual graph. It adds no source-numbered milestone and assumes none of these conclusions as graph-data fields. When $k=m/2$, the cardinality is $13m/2$.
--
--   Differences from the source:
--   - generalization: the fixed matrix supplied by Lemma 2.3 in the section 3 preamble → every binary matrix with exact row weight three and column weight six; reason: the structural results use only the exact weights and distinct nonzero columns; the source matrices satisfy these conditions
--   - encoding: parity-dependent assignment labels and arbitrary fixed row orderings → b-independent even-assignment labels interpreted as α + bⱼ, with increasing row and occurrence orderings; reason: this is the fixed-label oracle convention of section 3.3 and a permitted choice of fixed orderings; graphs remain uncolored and all bijections are allowed
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 9, §3.1 size and degree paragraph; p. 10, §3.3, equations (4)–(5)

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget

namespace GraphIsoTesting.FixedGraph

theorem gadget_interface {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) :
    Fintype.card (GadgetVertex m k) = 3 * k + 5 * m ∧
    DegreeBound (gadgetGraph A h b) 13 ∧
    ValidOracle (gadgetGraph A h b) 13 (gadgetOracle A h b) ∧
    (∀ i, vertexDegree (gadgetGraph A h b) (variableAnchor i) = 2) ∧
    (∀ i s, vertexDegree (gadgetGraph A h b) (valueVertex i s) = 13) ∧
    (∀ j, vertexDegree (gadgetGraph A h b) (constraintAnchor j) = 4) ∧
    (∀ j a, vertexDegree (gadgetGraph A h b) (assignmentVertex j a) = 4) := by sorry

end GraphIsoTesting.FixedGraph
