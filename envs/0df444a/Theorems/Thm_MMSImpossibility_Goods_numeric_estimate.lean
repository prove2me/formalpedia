-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_numeric_estimate
-- name    : MMSImpossibility.Goods.numeric_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:19:04.170202+00:00
-- url     : https://prove2.me/theorems/d8ba6705-ccd0-4613-8e41-c9f130a46f1d
-- title:
--   §2.3 — $1/(4896k^2) \ge 1/(396576\log_2^2 n) > 1/(400000\log_2^2 n)$
-- statement:
--   Let $n\ge 2^{16}$ and $k = 8\lceil\log_2 n\rceil$. Then
--
--   $$\frac{k/24}{204k^3} = \frac{1}{4896k^2}, \qquad k \le 9\log_2 n,$$
--
--   and
--
--   $$\frac{1}{4896k^2} \ge \frac{1}{396576\,\log_2^2 n} > \frac{1}{400000\,\log_2^2 n}.$$
--
--   This converts the additive shortfall $k/24$ of Proposition 8 against $\mathrm{MMS}_i = 204k^3$ into the explicit relative bound of Theorem 1.
--
--   Differences from the source:
--   - encoding: log(n), base 2 throughout the paper; ⌈log n⌉ → Real.logb 2 n; Nat.clog 2 n; reason: Nat.clog 2 n = ⌈log₂ n⌉ for n ≥ 1; same values
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §2.3 Putting It All Together, PDF p. 12 (printed p. 11)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- §2.3 (PDF p. 12), for `n ≥ 2^16` and `k = 8⌈log₂ n⌉`:
`(k/24)/(204k³) = 1/(4896k²)`, `k ≤ 9 log₂ n`, and
`1/(4896k²) ≥ 1/(396576 log₂² n) > 1/(400000 log₂² n)`. -/
theorem numeric_estimate (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    ((kOf n : ℝ) / 24) / (204 * (kOf n : ℝ) ^ 3) = 1 / (4896 * (kOf n : ℝ) ^ 2) ∧
    (kOf n : ℝ) ≤ 9 * Real.logb 2 n ∧
    1 / (396576 * Real.logb 2 n ^ 2) ≤ 1 / (4896 * (kOf n : ℝ) ^ 2) ∧
    1 / (400000 * Real.logb 2 n ^ 2) < 1 / (396576 * Real.logb 2 n ^ 2) := by sorry

end MMSImpossibility.Goods
