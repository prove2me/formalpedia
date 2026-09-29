-- Prove2me | Theorems.Thm_HighDimProb_RandomMatrices_covering_numbers_of_euclidean_ball_and_sphere
-- name    : HighDimProb.RandomMatrices.covering_numbers_of_euclidean_ball_and_sphere
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:22:18.675775+00:00
-- url     : https://prove2.me/theorems/792e373d-6167-4cee-be2b-849bba257578
-- title:
--   Corollary 4.2.13 — Covering numbers of the Euclidean ball and sphere
-- statement:
--   This is **Corollary 4.2.13**: the exponential-in-dimension covering number bound the goal
--   theorem's ε-net argument runs on (it is cited by name in the proof of Theorem 4.4.5 to
--   produce nets of cardinality $\le 9^n$, $9^m$).
--
--   The covering numbers of the unit Euclidean ball $B_2^n \subset \mathbb R^n$ satisfy, for
--   any $\varepsilon > 0$,
--
--   $$
--   \left(\frac{1}{\varepsilon}\right)^n \;\le\; N(B_2^n, \varepsilon) \;\le\;
--     \left(\frac{2}{\varepsilon} + 1\right)^n .
--   $$
--
--   The same upper bound holds for the unit Euclidean sphere $S^{n-1}$:
--   $N(S^{n-1}, \varepsilon) \le (2/\varepsilon + 1)^n$.
--
--   **Formalization Note** $N(K, \varepsilon)$ is the companion definition `coveringNumber`. No
--   absolute constant appears in this statement (unlike the goal theorem); both bounds are
--   exact in the book. `n : ℕ` is required positive to match the ambient dimension being a
--   genuine Euclidean space of dimension $\ge 1$ (§4.2's discussion is implicitly about
--   $\mathbb R^n$ for $n \ge 1$; at $n = 0$ every set is a single point and the statement would
--   need separate, uninteresting bookkeeping the book does not address).
-- source:
--   Vershynin, High-Dimensional Probability (2018), Corollary 4.2.13, p. 85 (PDF p. 93)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Definitions.Def_HighDimProb_RandomMatrices_coveringNumber

namespace HighDimProb.RandomMatrices

/-- **Corollary 4.2.13** (Covering numbers of the Euclidean ball), Vershynin,
*High-Dimensional Probability* (2018), p. 85.

The covering numbers of the unit Euclidean ball `B₂ⁿ` satisfy, for any `ε > 0`,
`(1/ε)ⁿ ≤ N(B₂ⁿ, ε) ≤ (2/ε + 1)ⁿ`. The same upper bound is true for the unit Euclidean
sphere `Sⁿ⁻¹`. -/
theorem covering_numbers_of_euclidean_ball_and_sphere (n : ℕ) (hn : 0 < n) (ε : ℝ)
    (hε : 0 < ε) :
    (1 / ε) ^ n ≤ (coveringNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ε : ℝ) ∧
    (coveringNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ε : ℝ)
        ≤ (2 / ε + 1) ^ n ∧
    (coveringNumber (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ε : ℝ)
        ≤ (2 / ε + 1) ^ n := by sorry

end HighDimProb.RandomMatrices
