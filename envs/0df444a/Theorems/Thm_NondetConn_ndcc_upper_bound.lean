-- Prove2me | Theorems.Thm_NondetConn_ndcc_upper_bound
-- name    : NondetConn.ndcc_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:28:19.705951+00:00
-- url     : https://prove2.me/theorems/c6b93afc-93ca-484f-a6e1-23f4bbf125fc
-- title:
--   Section 4 — upper bound $N(\mathsf{bConn}_N) \le \lceil\log_2 n!\rceil$
-- statement:
--   Let $N = 2n$ with $n \ge 1$. Then
--   $$
--   N(\mathsf{bConn}_N) \le \lceil \log_2 n! \rceil .
--   $$
--   In the paper's words, the upper bound follows from a simple one-way deterministic protocol that communicates to Bob a spanning forest of Alice's edges: Alice's edges form the perfect matching $a$, which is its own spanning forest, and sending it costs $\lceil\log_2 n!\rceil = O(N\log N)$ bits. In the cover model the protocol is the cover by the $n!$ rectangles $\{a\}\times\{b : \mathsf{bConn}_N(a,b) = 1\}$.
--
--   This is the $O(N\log N)$ half of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: the upper bound follows from a one-way deterministic protocol sending a spanning forest of Alice's edges → ndcc (bConn n) ≤ Nat.clog 2 n!; reason: the protocol sends a, one of n! messages; its 1-certificate form is the cover by n! rectangles {a} × {b | bConn n a b}
--   - encoding: [n], b⁻¹a, n = N/2 → Fin n (0-based), b⁻¹ * a (apply a first), bConn n; reason: Lean conventions; same instances
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_ndcc

namespace NondetConn

/-- **Section 4, the upper bound** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), p.8: "The upper bound
follows from a simple one-way deterministic protocol that communicates to Bob a spanning forest of
Alice's edges").
For `n ≥ 1`, `N(bConn_N) ≤ ⌈log₂ n!⌉` (`N = 2n`).

**Formalization Note** Alice's edges form the perfect matching `a`, which is its own spanning
forest; sending it costs `⌈log₂ n!⌉` bits. In the cover model this protocol is the cover by the
`n!` rectangles `{a} × {b | bConn_N(a, b)}`. -/
theorem ndcc_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    ndcc (bConn n) ≤ Nat.clog 2 n.factorial := by sorry

end NondetConn
