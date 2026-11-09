-- Prove2me | Theorems.Thm_NondetConn_theorem_4_1
-- name    : NondetConn.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:28:05.423798+00:00
-- url     : https://prove2.me/theorems/a04500b8-2f7a-4e19-87ea-45b7c1e7e602
-- title:
--   Theorem 4.1 — $N(\mathsf{bConn}_N) = \Theta(N\log N)$
-- statement:
--   For even $N > 1$, the nondeterministic communication complexity of bipartite connectivity satisfies
--   $$
--   N(\mathsf{bConn}_N) = \Theta(N\log N),
--   $$
--   regardless of the number of rounds. Precisely: there are constants $c, C > 0$ and $N_0$ such that for every even $N \ge N_0$,
--   $$
--   c\,N\log_2 N \le N(\mathsf{bConn}_N) \le C\,N\log_2 N .
--   $$
--   Here $\mathsf{bConn}_N(a,b) = 1$ iff $b^{-1}a$ is a single $(N/2)$-cycle, for permutations $a, b$ of $[N/2]$ (two perfect matchings across a balanced bipartition), and $N(f) = \lceil\log_2 C^1(f)\rceil$ is the logarithm of the least number of 1-monochromatic rectangles covering $f^{-1}(1)$.
--
--   This settles the nondeterministic communication complexity of graph connectivity, improving the $\Omega(N\log\log N)$ lower bound of Raz and Spieker and resolving their conjecture.
--
--   Differences from the source:
--   - reading: "for even N > 1, N(bConn_N) = Θ(N log N)" → ∃ c C > 0, ∃ N₀, ∀ even N ≥ N₀, c·N·log₂N ≤ N(bConn_N) ≤ C·N·log₂N; reason: Θ is asymptotic; the uniform reading over all even N > 1 is false for every c > 0, since N(bConn₂) = 0 (n = 1 has a single input)
--   - encoding: N(·), "regardless of the number of rounds" → ndcc = Nat.clog 2 of the 1-rectangle cover number; reason: the standard round-free characterization of nondeterministic complexity (Kushilevitz–Nisan, Ch. 2); other conventions differ by O(1), absorbed by Θ
--   - encoding: bConn_N on permutations of [N/2], b⁻¹a a single (N/2)-cycle → bConn (N / 2) on Equiv.Perm (Fin (N/2)), conn via SameCycle of b⁻¹ * a; reason: Lean conventions; same instances for even N
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem 4.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_ndcc

namespace NondetConn

/-- **Theorem 4.1** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4, p.9).
For even `N > 1`, the nondeterministic communication complexity of `bConn_N` is
`N(bConn_N) = Θ(N log N)`, regardless of the number of rounds: there are constants
`c, C > 0` and `N₀` such that for every even `N ≥ N₀`,
`c · N log₂ N ≤ N(bConn_N) ≤ C · N log₂ N`.

**Formalization Note** `bConn_N` is `bConn (N / 2)` (permutations of `Fin (N/2)`), and `N(·)`
is `ndcc`, the ceiling of `log₂` of the 1-rectangle cover number (round-free). `Θ` is read with a threshold
`N₀`: a bound for all even `N > 1` with `c > 0` is false at `N = 2`, where `N(bConn₂) = 0`. -/
theorem theorem_4_1 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
    c * N * Real.logb 2 N ≤ (ndcc (bConn (N / 2)) : ℝ) ∧
      (ndcc (bConn (N / 2)) : ℝ) ≤ C * N * Real.logb 2 N := by sorry

end NondetConn
