-- Prove2me | Theorems.Thm_KLZ97_overhead_polylog
-- name    : KLZ97.overhead_polylog
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:17:13.594028+00:00
-- url     : https://prove2.me/theorems/34b1fc98-05de-4f03-863e-53483badc724
-- title:
--   Polylogarithmic overhead: $K^{\lceil \log_2 L\rceil} \le K L^{\log_2 K}$
-- statement:
--   The overhead estimate of Section II.F. With $K$ a bound on the resources one encoded gate consumes at the level below, a concatenation depth of $h = \lceil \log_2 L \rceil$ levels costs $K^{h}$ resources per computational gate, and this is at most
--   $$K \cdot L^{\log_2 K}.$$
--   Applied with $L = \log_{1/(fp)}(n/q)$ this is the paper's conclusion that the overhead is polylogarithmic in $n$ and $1/q$, with exponent $\log_2 K$.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Section II.F (Overheads), p. 9

import Mathlib
import Definitions.Def_KLZ97_model

namespace KLZ97

theorem overhead_polylog (K L : ℝ) (hK : 2 ≤ K) (hL : 1 ≤ L) :
    K ^ (⌈Real.logb 2 L⌉₊) ≤ K * L ^ Real.logb 2 K := by sorry

end KLZ97
