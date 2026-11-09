-- Prove2me | Theorems.Thm_NondetConn_lemma_4_3
-- name    : NondetConn.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:31:04.611081+00:00
-- url     : https://prove2.me/theorems/7bd691d2-1849-47f8-8e3a-ce14a55e72e5
-- title:
--   Lemma 4.3 — $(1 + \frac{1}{4n}) S_n \le S_{n-1} + 2\log n + O(\log\log n)$
-- statement:
--   For $n > 1$,
--   $$
--   \Bigl(1 + \frac{1}{4n}\Bigr) \cdot S_n \le S_{n-1} + 2\log_2 n + O(\log\log n),
--   $$
--   where $S_n$ is the log-size of the largest 1-monochromatic rectangle of $\mathsf{bConn}_{2n}$. Precisely: there is a constant $K$ such that for every $n \ge 2$, $(1 + \frac{1}{4n}) S_n \le S_{n-1} + 2\log_2 n + K\log_2\log_2 n$.
--
--   Solving this recurrence gives $S_n \le \frac85 n\log n + O(n\log\log n)$, which is strictly below $\log T \approx 2n\log n$ and yields the lower bound of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: n > 1; O(log log n) → 2 ≤ n; ∃ K, ∀ n ≥ 2, K · log₂ log₂ n; reason: n > 1 in ℕ; for n ≥ 3, log₂log₂n ≥ 0.66 absorbs finitely many n and constants, and at n = 2 the inequality holds with no error term (S₂ = S₁ = 0)
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Lemma 4.3, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_NondetConn_S

namespace NondetConn

/-- **Lemma 4.3** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4, p.9).
For `n > 1`, `(1 + 1/(4n)) · S_n ≤ S_{n−1} + 2 log n + O(log log n)`.

**Formalization Note** Logarithms are base 2; `O(log log n)` is `K · log₂ log₂ n` with one
constant `K` for all `n ≥ 2` (at `n = 2`, `log₂ log₂ 2 = 0` and the inequality holds since
`S₂ = S₁ = 0`). -/
theorem lemma_4_3 : ∃ K : ℝ, ∀ n : ℕ, 2 ≤ n →
    (1 + 1 / (4 * (n : ℝ))) * S n ≤ S (n - 1) + 2 * Real.logb 2 n
      + K * Real.logb 2 (Real.logb 2 n) := by sorry

end NondetConn
