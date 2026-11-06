-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_slow_mixing_short_cycles
-- name    : KawasakiSOS.Threshold.slow_mixing_short_cycles
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:06:23.717908+00:00
-- url     : https://prove2.me/theorems/eaa67c02-4f70-495c-82eb-293942adaba4
-- title:
--   Proposition 1.4: slow mixing for $k\le4$
-- statement:
--   Let $\lambda>1$ and $k\le n$. Then the lazy Kawasaki chain satisfies
--
--   $$\tau(1/4)\ge\begin{cases}\lambda^{2n-4}&\text{if }k=2,\\[2pt]\dfrac{\lambda^{n-1}}{(n+1)(n+2)}&\text{if }k=3,\\[6pt]\dfrac{2\lambda^{n-1}}{(n+2)^2}&\text{if }k=4.\end{cases}$$
--
--   These are the lower bounds of the threshold: below $k=5$ an energy barrier of order $n$ separates the high-weight states. The source's closing sentence, that the mixing time is at least exponential in $n$, is the lower bound in clause (i) of the goal theorem.
--
--   Differences from the source:
--   - reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain; reason: the source does not define the term; this is the standard meaning, as in its reference [LPW17]
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Proposition 1.4, p. 5 (PDF p. 6)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_tau

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Proposition 1.4, p. 5 (PDF p. 6).

Formalization Notes:
- reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain. The source does not define the term; this is the standard meaning, as in its reference [LPW17]. -/
theorem slow_mixing_short_cycles {n k : ℕ} [NeZero k] (hk : 2 ≤ k) (hkn : k ≤ n) {lam : ℝ} (hlam : 1 < lam) :
    (k = 2 → lam ^ (2 * n - 4) ≤ (tau n k lam (1 / 4) : ℝ)) ∧
      (k = 3 → lam ^ (n - 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ (tau n k lam (1 / 4) : ℝ)) ∧
      (k = 4 → 2 * lam ^ (n - 1) / ((n : ℝ) + 2) ^ 2 ≤ (tau n k lam (1 / 4) : ℝ)) := by sorry

end KawasakiSOS.Threshold
