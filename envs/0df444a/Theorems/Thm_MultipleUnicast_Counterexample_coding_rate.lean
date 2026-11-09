-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_coding_rate
-- name    : MultipleUnicast.Counterexample.coding_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:59.453208+00:00
-- url     : https://prove2.me/theorems/22053705-61db-496d-9c82-57c18859a5e8
-- title:
--   Section 4, unnumbered R_code ≥ 1 — causal linear rate-one witness
-- statement:
--   The specified network has 157 sessions. Its computed code is causal and $\mathbb F_9$-linear, transmits once on each physical edge, and recovers every source message for every input tuple through the stated local destination decoder. Each local interpolation uses exactly five available values and is a linear inverse to their evaluation map. With independent uniform field messages and positive scale $c^*=\log_2 9$, the code satisfies the §2 rate-one inequalities. Consequently,
--   $$R_{\mathrm{code}}\ge1.$$
--   The supremum in this conclusion is over all valid chronological codes and all discrete independent source laws. The finite linear witness does not restrict that class. The grouped arc entropy convention gives the rate without a permanent loss from the finite startup order.
--
--   Differences from the source:
--   - encoding: the source labels vertices and candidate edges by integers and sessions by B → Fin 182 and Fin 910 labels, with a fixed equivalence B ≃ Fin (card B) where needed; reason: the same finite objects and source/sink order are retained
--   - encoding: the unique local interpolation and its causal computation → classical solving with a zero off-domain default, plus solvability, linearity and computation as conclusions; reason: uniqueness on every available input eliminates the total-function fallback on all executions
--   - encoding: Shannon entropy and the supremal common coding rate over all source laws and valid codes → arbitrary discrete PMF laws, base-two extended nonnegative entropy and an ENNReal throughput supremum; reason: no finite-alphabet or linear-code restriction; infinite entropy is retained and the positive scale absorbs the fixed base
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §4, unnumbered R_code ≥ 1 display, PDF p. 10 / printed p. 9; protocol and correctness, PDF pp. 11–12 / printed pp. 10–11; §2, PDF pp. 4–5 / printed pp. 3–4

import Definitions.Def_MultipleUnicast_Counterexample_Protocol

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample

/-- §4: the concrete all-input zero-error F₉-linear causal code attains rate one. -/
theorem coding_rate :
    network.k = 157 ∧ CausalLinearCode ∧
    0 < witnessScale ∧ SupportsRate protocol witnessLaw 1 witnessScale ∧
    (1 : ENNReal) ≤ codingThroughput network := by sorry

end MultipleUnicast.Counterexample
