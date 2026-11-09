-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_5_5
-- name    : OnlineRealSampling.Exact.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:59.988672+00:00
-- url     : https://prove2.me/theorems/e7b2c0e3-47a9-488b-9c7d-24bd07be3d22
-- title:
--   Proposition 5.5 — tail of the final precision
-- statement:
--   Let $F$ have a valid oracle, $M\ge1$, $Z$ uniform on $\{0,\dots,M-1\}$ and independent of the fair bits, and $k\in\mathbb N$. The final value of $t$ in IntervalSample$(F,(Z,M))$ satisfies
--   $$\Pr(t>k\mid X,M)\le\frac{6}{2^kf(X)}.\qquad(21)$$
--
--   The bound controls the number of iterations, the oracle precision and the fresh bits read by IntervalSample.
--
--   Differences from the source:
--   - encoding: a bound conditional on X = x → the integral over the event {X = x} is at most the bound times Pr(X = x), for every x with f(x) > 0; reason: equivalent on the fibres of positive probability, which are exactly those with f(x) > 0
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 5.5, PDF 11 / printed 10; proof PDF 11–12 / printed 10–11

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 5.5 (tail of the final precision). For every `k ∈ ℕ`, the final value of `t` in
`IntervalSample(F, (Z, M))` satisfies `Pr(t > k | X, M) ≤ 6 / (2^k f(X))`; stated on every fibre
`X = x` with `f(x) > 0`. -/
theorem proposition_5_5 (w : ℕ) (O : CDFOracle) (hO : O.Valid) (M : ℕ) (hM : 1 ≤ M) (x : ℕ)
    (hx : 0 < pmf O.F x) (k : ℕ) :
    stepMeasure M {p | ∃ c : Config ISState, intervalSampleOn w O.toOracleAccess M p = some c ∧
        c.st.lo = x ∧ k < c.st.t} ≤
      ENNReal.ofReal (6 / (2 ^ k * pmf O.F x)) * stepMeasure M (isEvent w O.toOracleAccess M x) := by sorry

end OnlineRealSampling.Exact
