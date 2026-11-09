-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_multiple_unicast_coding_advantage
-- name    : MultipleUnicast.Counterexample.multiple_unicast_coding_advantage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:29.559215+00:00
-- url     : https://prove2.me/theorems/dee16fbc-f2db-43de-854d-4dbba503a80d
-- title:
--   Theorem 1.1 and Section 4 — complete explicit causal coding advantage
-- statement:
--   The concrete $\mathbb F_9$ incidence construction, with Appendix A's deletions and vertex order, gives an undirected network with 182 vertices, 735 physical unit-capacity edges and 157 independent unit-demand sessions. Its deterministic causal $\mathbb F_9$-linear code uses each physical edge once and its actual local decoder recovers the demanded source message for every possible input tuple. Uniform independent field messages support common rate one at positive scale $\log_2 9$.
--
--   Over the full §2 class of codes and source laws, and over all nonnegative real fractional flows with shared both-direction edge capacity,
--   $$R_{\mathrm{code}}\ge1,\qquad 0<R_{\mathrm{flow}}\le\frac{147}{157},\qquad \frac{R_{\mathrm{code}}}{R_{\mathrm{flow}}}\ge\frac{157}{147}>1.$$
--   The nonnegative feasible flow-rate set is nonempty and bounded, a positive rate is feasible, and the bound applies to every feasible real flow. The conclusion also verifies the field size, candidate-edge indexing, terminal distinctness, exact demands, and symmetric 0/1 capacities.
--
--   This is Theorem 1.1's existential separation witnessed by the full quantitative construction in the abstract and §4. The theorem has no successful-code, dimension, isomorphism or routing-bound hypotheses. Deleted edges are not resources, and no code class or routing domain is narrowed.
--
--   Differences from the source:
--   - encoding: Theorem 1.1 existential advantage, realized by the abstract and Section 4 fixed witness → one conjunction verifying that exact constructed network and protocol, its counts, all-input recovery, rate bounds and gap; reason: an explicit verified witness yields the existential claim while retaining every quantitative clause
--   - encoding: the source labels vertices and candidate edges by integers and sessions by B → Fin 182 and Fin 910 labels, with a fixed equivalence B ≃ Fin (card B) where needed; reason: the same finite objects and source/sink order are retained
--   - encoding: the unique local interpolation and its causal computation → classical solving with a zero off-domain default, plus solvability, linearity and computation as conclusions; reason: uniqueness on every available input eliminates the total-function fallback on all executions
--   - encoding: Shannon entropy and the supremal common coding rate over all source laws and valid codes → arbitrary discrete PMF laws, base-two extended nonnegative entropy and an ENNReal throughput supremum; reason: no finite-alphabet or linear-code restriction; infinite entropy is retained and the positive scale absorbs the fixed base
--   - encoding: fractional routing with arbitrary real splitting and shared undirected capacity → published nonnegative real arc flows, with exact conservation and summed both-direction capacity; nonempty bounded feasible rates and positive feasibility are conclusions; reason: the equivalent arc representation and explicit supremum guards preserve all routing instances
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, Theorem 1.1, PDF p. 2 / printed p. 1, together with abstract, PDF p. 1 (unnumbered), and full quantitative witness in §4, PDF pp. 10–12 / printed pp. 9–11; Appendix A, PDF pp. 14–15 / printed pp. 13–14

import Definitions.Def_MultipleUnicast_Counterexample_Protocol

set_option maxRecDepth 2048
open scoped Classical

namespace MultipleUnicast.Counterexample

/-- Theorem 1.1 together with the complete quantitative §4 witness, PDF 2, 10–12.
All data are constructed: this theorem has no successful-code or dimension hypotheses. -/
theorem multiple_unicast_coding_advantage :
    Fintype.card F9 = 9 ∧ Fintype.card Vertex = 182 ∧
    incidenceList.length = 910 ∧ Function.Injective edgePair ∧
    physical.card = 735 ∧ network.k = 157 ∧
    (∀ i, network.D i = 1 ∧ network.s i ≠ network.t i) ∧
    (∀ u v, network.C u v = if graph.Adj u v then 1 else 0) ∧
    CausalLinearCode ∧
    (∀ m i, protocol.decode i (ownValues (network.t i) m)
      (received protocol (network.t i) m) = m i) ∧
    0 < witnessScale ∧ SupportsRate protocol witnessLaw 1 witnessScale ∧
    (1 : ENNReal) ≤ codingThroughput network ∧
    feasibleRates.Nonempty ∧ BddAbove feasibleRates ∧
    (∃ r : ℝ, 0 < r ∧ ∃ f, network.IsFeasibleFlow f r) ∧
    (∀ (r : ℝ) (f : Fin network.k → Vertex → Vertex → ℝ),
      0 ≤ r → network.IsFeasibleFlow f r → r ≤ (147 : ℝ) / 157) ∧
    0 < routingThroughput ∧ routingThroughput ≤ (147 : ℝ) / 157 ∧
    ENNReal.ofReal ((157 : ℝ) / 147) ≤
      codingThroughput network / ENNReal.ofReal routingThroughput ∧
    (1 : ℝ) < (157 : ℝ) / 147 := by sorry

end MultipleUnicast.Counterexample
