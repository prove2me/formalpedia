-- Prove2me | Theorems.Thm_FowlerLSQC_Shor_measurementProb_of_dvd
-- name    : FowlerLSQC.Shor.measurementProb_of_dvd
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:16.711077+00:00
-- url     : https://prove2.me/theorems/9d6204d3-77f8-4bb0-9404-14eeb993a2a8
-- title:
--   Exact peaks of (7.7) when $r\mid 2^{2L}$
-- statement:
--   Let $L\ge0$ and let $r$ be a divisor of $2^{2L}$. Let $\Pr(j,r,L)$ be the outcome probability (7.7) of quantum period finding. Then:
--
--   1. for every integer $0\le c<r$,
--   $$
--   \Pr\!\Big(c\,\frac{2^{2L}}{r},\,r,\,L\Big)=\frac1r;
--   $$
--   2. for every $0\le j<2^{2L}$ that is not of the form $c\,2^{2L}/r$ with $0\le c<r$, $\Pr(j,r,L)=0$.
--
--   So when $r$ divides $2^{2L}$ the measurement returns one of the $r$ exact multiples of $2^{2L}/r$, each with probability $1/r$.
--
--   **Formalization Note** $r\mid 2^{2L}$ forces $r\ge1$. The measurable values are $0\le j<2^{2L}$, the basis states of the $2L$-qubit register in (7.6).
--
--   Differences from the source:
--   - generalization: $r$ the period of $f(k)=m^k\bmod N$ → any divisor $r$ of $2^{2L}$; reason: (7.7) depends on $r$ and $L$ only, and the period of a function with $r\mid 2^{2L}$ is a special case
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, Ch. 7, Eq. (7.7), p.79 (PDF p.97)

import Mathlib
import Definitions.Def_FowlerLSQC_Shor_measurementProb

namespace FowlerLSQC.Shor

/-- Exact peaks of (7.7) when `r` divides `2^{2L}`, Fowler, *Towards Large-Scale Quantum
Computation*, arXiv:quant-ph/0506126v1, Ch. 7, (7.7), p.79 (PDF 97): "If r divides 2^{2L},
Eq. (7.7) can be evaluated exactly. In this case the probability of observing j = c2^{2L}/r for
some integer 0 ≤ c < r is 1/r whereas if j ≠ c2^{2L}/r the probability is 0."

Both clauses: (1) for every integer `0 ≤ c < r`, `Pr(c·2^{2L}/r, r, L) = 1/r`; (2) every
measurable value `j` (`0 ≤ j < 2^{2L}`, the range of the `k`-register in (7.6)) that is not of the
form `c·2^{2L}/r` with `0 ≤ c < r` has `Pr(j, r, L) = 0`.

**Formalization Note** `r ∣ 2^{2L}` forces `r ≥ 1`, so no positivity hypothesis is needed;
`c·2^{2L}/r` is written `c * (2^(2L) / r)`, an exact `ℕ` quotient under the divisibility. The
statement holds for every such `r`, not only for the period of some `m^k mod N`. -/
theorem measurementProb_of_dvd (r L : ℕ) (hr : r ∣ 2 ^ (2 * L)) :
    (∀ c : ℕ, c < r → measurementProb (c * (2 ^ (2 * L) / r)) r L = 1 / (r : ℝ)) ∧
    (∀ j : ℕ, j < 2 ^ (2 * L) → (∀ c : ℕ, c < r → j ≠ c * (2 ^ (2 * L) / r)) →
      measurementProb j r L = 0) := by sorry

end FowlerLSQC.Shor
