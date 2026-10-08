-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_expected_max_exponential
-- name    : KalaiVempala.Multiplicative.expected_max_exponential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:37.088596+00:00
-- url     : https://prove2.me/theorems/02122ccc-7326-4b10-b308-3df83109fcf0
-- title:
--   End of §2, p. 299 — the expected maximum of n standard exponentials is at most ln n + 1
-- statement:
--   Let $n \ge 1$ and let $x_1, \dots, x_n$ be independent random variables, each with the standard exponential distribution (density $e^{-x}$ on $[0,\infty)$, mean $1$). Then
--   $$\mathbb E\big[\max(x_1, \dots, x_n)\big] \;\le\; \ln n + 1 .$$
--
--   The paper uses this to bound the expected size of the FPL\* perturbation: after scaling by $1/\varepsilon$ it gives the $(1 + \ln n)/\varepsilon$ term of Theorem 1.1(b).
--
--   **Formalization Note** The joint law is the product `Measure.pi` of $n$ copies of Mathlib's `ProbabilityTheory.expMeasure 1`, and the maximum is `Finset.univ.sup'` over `Fin n`. The hypothesis $n \ge 1$ (`[NeZero n]`) is added because a maximum over an empty index set is undefined; the page tacitly has $n \ge 1$. The maximum is integrable (it is bounded by $x_1 + \dots + x_n$), so the integral is the true expectation.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 299, end of §2 (display after 'The expected maximum is')

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem expected_max_exponential {n : ℕ} [NeZero n] :
    ∫ x, Finset.univ.sup' Finset.univ_nonempty x
        ∂(Measure.pi fun _ : Fin n => ProbabilityTheory.expMeasure 1) ≤ Real.log n + 1 := by sorry

end KalaiVempala.Multiplicative
