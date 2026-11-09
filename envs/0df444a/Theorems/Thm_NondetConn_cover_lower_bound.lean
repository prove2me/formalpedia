-- Prove2me | Theorems.Thm_NondetConn_cover_lower_bound
-- name    : NondetConn.cover_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:31:58.454203+00:00
-- url     : https://prove2.me/theorems/40a6ec92-5b1f-4ca8-8e32-d0fb24ee5f1f
-- title:
--   Proof of Theorem 4.1 — every 1-cover of $\mathsf{bConn}_N$ has at least $T/2^{S_n}$ rectangles
-- statement:
--   Let $N = 2n$ with $n \ge 1$ and $T = n!\,(n-1)!$. If $k$ 1-monochromatic rectangles cover $\mathsf{bConn}_N^{-1}(1)$, then
--   $$
--   k \ge \frac{T}{2^{S_n}} .
--   $$
--
--   Each rectangle covers at most $2^{S_n}$ of the $T$ one-inputs; with Lemma 4.3 this gives the $\Omega(N\log N)$ lower bound of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: a fixed, sufficiently large n = N/2 → every n ≥ 1; reason: the counting argument uses no largeness; it specializes to large n
--   - encoding: "at least T/2^{S_n} rectangles are required to cover bConn⁻¹(1)" → every k and every cover R : Fin k → Set × Set with IsOneRectangleCover (bConn n) R satisfy T / 2^{S n} ≤ k; reason: the published cover predicate; rectangles are arbitrary sets of permutations
--   - encoding: [n], b⁻¹a, n = N/2 → Fin n (0-based), b⁻¹ * a (apply a first), bConn n; reason: Lean conventions; same instances
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Theorem 4.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_S
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix

namespace NondetConn

/-- **Proof of Theorem 4.1, cover bound** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), p.10).
At least `T / 2^{S_n}` 1-monochromatic rectangles are required to cover `bConn_N⁻¹(1)`, where
`T = n!(n − 1)!` and `N = 2n`: every cover of `bConn_N⁻¹(1)` by `k` 1-monochromatic rectangles
has `k ≥ T / 2^{S_n}`.

**Formalization Note** Rectangles are pairs of arbitrary sets of permutations, as in the published
cover predicate `ExtensionComplexity.TSP.IsOneRectangleCover`; `2^{S_n}` is a real power. -/
theorem cover_lower_bound (n : ℕ) (hn : 1 ≤ n) (k : ℕ)
    (R : Fin k → Set (Equiv.Perm (Fin n)) × Set (Equiv.Perm (Fin n)))
    (hR : ExtensionComplexity.TSP.IsOneRectangleCover (bConn n) R) :
    (n.factorial * (n - 1).factorial : ℝ) / (2 : ℝ) ^ S n ≤ k := by sorry

end NondetConn
