-- Prove2me | Theorems.Thm_NondetConn_f_closed_form
-- name    : NondetConn.f_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:24.779556+00:00
-- url     : https://prove2.me/theorems/002de6c5-5540-472f-a4a8-d73b71ec0df0
-- title:
--   Proof of Theorem 4.1 — $f_n = \sum_{i\in[n]}\prod_{j\in[i,n]} \frac{4j}{4j+1} = \frac{4n}{5}$
-- statement:
--   For $n \ge 1$ define
--   $$
--   f_n = \sum_{i \in [n]} \prod_{j \in [i,n]} \frac{4j}{4j+1}.
--   $$
--   Then $f_n = \dfrac{4n}{5}$.
--
--   The coefficient $f_n$ is what the recurrence of Lemma 4.3 accumulates when unrolled down to $S_1 = 0$; its closed form gives the constant $\frac85$ in the bound on $S_n$.
--
--   Differences from the source: none.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Theorem 4.1, p.10 (PDF p.12)

import Mathlib

namespace NondetConn

/-- **Proof of Theorem 4.1, `f_n = 4n/5`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), p.10).
For `n ≥ 1`, `f_n = ∑_{i ∈ [n]} ∏_{j ∈ [i, n]} 4j/(4j + 1) = 4n/5`. -/
theorem f_closed_form (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc i n, (4 * (j : ℝ)) / (4 * j + 1) = 4 * n / 5 := by sorry

end NondetConn
