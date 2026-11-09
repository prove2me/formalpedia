-- Prove2me | Theorems.Thm_NondetConn_S_upper_bound
-- name    : NondetConn.S_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:31:54.980813+00:00
-- url     : https://prove2.me/theorems/f0e7a91b-70d5-49c5-815c-64d279004fd6
-- title:
--   Proof of Theorem 4.1 — $S_n \le \frac85 n\log n + O(n\log\log n)$
-- statement:
--   Let $S_n$ be the log-size of the largest 1-monochromatic rectangle of $\mathsf{bConn}_{2n}$. Then
--   $$
--   S_n \le \frac85\, n\log_2 n + O(n\log\log n);
--   $$
--   precisely, there is a constant $K$ such that $S_n \le \frac85 n\log_2 n + K\, n\log_2\log_2 n$ for every $n \ge 2$.
--
--   Since the number of 1-inputs is $T = n!(n-1)! = 2^{(2-o(1))n\log n}$, this bound forces $2^{\Omega(n\log n)}$ rectangles in any cover.
--
--   Differences from the source:
--   - encoding: O(n log log n) → ∃ K, ∀ n ≥ 2, K · n · log₂ log₂ n; reason: for n ≥ 3, log₂log₂n > 0 absorbs finitely many n; at n = 2, S₂ = 0 ≤ 16/5 holds with no error term; n ≥ 2 keeps log₂log₂n defined
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Theorem 4.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_NondetConn_S

namespace NondetConn

/-- **Proof of Theorem 4.1, bound on `S_n`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), p.10).
`S_n ≤ (8/5) n log n + O(n log log n)`.

**Formalization Note** Logarithms are base 2; `O(n log log n)` is `K · n · log₂ log₂ n` with one
constant `K` for all `n ≥ 2`. -/
theorem S_upper_bound : ∃ K : ℝ, ∀ n : ℕ, 2 ≤ n →
    S n ≤ 8 / 5 * n * Real.logb 2 n + K * n * Real.logb 2 (Real.logb 2 n) := by sorry

end NondetConn
