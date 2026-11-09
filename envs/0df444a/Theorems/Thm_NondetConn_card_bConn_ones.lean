-- Prove2me | Theorems.Thm_NondetConn_card_bConn_ones
-- name    : NondetConn.card_bConn_ones
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:26:54.646863+00:00
-- url     : https://prove2.me/theorems/f3d18332-6507-4cd7-ae43-934899922410
-- title:
--   Proof of Theorem 4.1 — $\mathsf{bConn}_N$ has $T = n!\,(n-1)!$ one-inputs
-- statement:
--   Let $N = 2n$ with $n \ge 1$. The number of input pairs $(a,b) \in P_n \times P_n$ with $\mathsf{bConn}_N(a,b) = 1$ is
--   $$
--   T = n!\,(n-1)!.
--   $$
--
--   Together with the bound on rectangle sizes this counts how many rectangles a cover needs.
--
--   Differences from the source:
--   - generalization: a fixed, sufficiently large n = N/2 → every n ≥ 1; reason: the count is exact for every n ≥ 1 (the paper's bijection (c, b) ↦ (bc, b) uses no largeness); it specializes to large n
--   - encoding: [n], b⁻¹a, n = N/2 → Fin n (0-based), b⁻¹ * a (apply a first), bConn n; reason: Lean conventions; same instances
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Theorem 4.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_NondetConn_bConn

namespace NondetConn

/-- **Proof of Theorem 4.1, the number of 1-inputs** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), p.9).
The number of input pairs `a, b ∈ P_n` with `bConn_N(a, b) = 1` (`N = 2n`) is
`T = n! (n − 1)!`. Stated for every `n ≥ 1`. -/
theorem card_bConn_ones (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) => bConn n p.1 p.2)).card
      = n.factorial * (n - 1).factorial := by sorry

end NondetConn
