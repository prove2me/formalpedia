-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_flow_bound
-- name    : MultipleUnicast.Counterexample.flow_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:14.562806+00:00
-- url     : https://prove2.me/theorems/6c20b3ef-5bdf-4007-b2fe-82316875aca0
-- title:
--   Section 4, unnumbered throughput chain — universal real-flow upper bound
-- statement:
--   For the constructed unit-capacity instance, the nonnegative feasible real common rates form a nonempty bounded set, and a strictly positive rate is feasible. Every nonnegative real rate $r$ and every feasible real arc flow $f$ satisfy $r\le147/157$. In particular,
--   $$0<R_{\mathrm{flow}}\le\frac{735}{785}=\frac{147}{157}<1\le R_{\mathrm{code}}.$$
--   Flows may split arbitrarily; conservation is exact, and capacity is summed over all sessions and both orientations. The nonempty, bounded and positive-feasibility conclusions ensure that the routing supremum is an actual finite positive quantity. The final coding-rate clause retains the complete displayed chain.
--
--   Differences from the source:
--   - encoding: fractional routing with arbitrary real splitting and shared undirected capacity → published nonnegative real arc flows, with exact conservation and summed both-direction capacity; nonempty bounded feasible rates and positive feasibility are conclusions; reason: the equivalent arc representation and explicit supremum guards preserve all routing instances
--   - encoding: Shannon entropy and the supremal common coding rate over all source laws and valid codes → arbitrary discrete PMF laws, base-two extended nonnegative entropy and an ENNReal throughput supremum; reason: no finite-alphabet or linear-code restriction; infinite entropy is retained and the positive scale absorbs the fixed base
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §4, unnumbered R_flow ≤ 735/785 = 147/157 < 1 ≤ R_code display, PDF p. 10 / printed p. 9; distance argument, PDF p. 12 / printed p. 11

import Definitions.Def_MultipleUnicast_Counterexample_Protocol

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample

/-- §4 full throughput chain, with the real-flow supremum's nondegeneracy obligations. -/
theorem flow_bound :
    feasibleRates.Nonempty ∧ BddAbove feasibleRates ∧
    (∃ r : ℝ, 0 < r ∧ ∃ f, network.IsFeasibleFlow f r) ∧
    (∀ (r : ℝ) (f : Fin network.k → Vertex → Vertex → ℝ),
      0 ≤ r → network.IsFeasibleFlow f r → r ≤ (147 : ℝ) / 157) ∧
    0 < routingThroughput ∧
    routingThroughput ≤ (735 : ℝ) / 785 ∧
    (735 : ℝ) / 785 = (147 : ℝ) / 157 ∧
    (147 : ℝ) / 157 < 1 ∧ (1 : ENNReal) ≤ codingThroughput network := by sorry

end MultipleUnicast.Counterexample
