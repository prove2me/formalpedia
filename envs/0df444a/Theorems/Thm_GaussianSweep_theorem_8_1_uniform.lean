-- Prove2me | Theorems.Thm_GaussianSweep_theorem_8_1_uniform
-- name    : GaussianSweep.theorem_8_1_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:43.288094+00:00
-- url     : https://prove2.me/theorems/a8290ef7-0abf-4670-80e1-580011edb596
-- title:
--   Proof of Theorem 8.1 — uniform statement: $\mathrm{pw}(G) \le (c_3 + \varepsilon)n$ for $n \ge N(\varepsilon)$
-- statement:
--   For every $\varepsilon > 0$ there is $N(\varepsilon)$ such that every graph $G$ with $\Delta(G) \le 3$ and $n \ge N(\varepsilon)$ vertices satisfies
--   $$
--   \mathrm{pw}(G) \le (c_3 + \varepsilon)\, n, \qquad c_3 = \frac{3}{4\pi}\arccos\frac56 .
--   $$
--   The graph may be disconnected and may have vertices of degree $0$, $1$ or $2$. This is the form in which the paper proves Theorem 8.1; the $o(n)$ form follows by taking the worst graph on $n$ vertices.
--
--   Differences from the source:
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
--   - encoding: pw(G) ≤ (c₃ + ε)n → (pathwidth G : ℝ) ≤ (c3 + ε) * card V, with pathwidth ℤ-valued; reason: the integer is compared in ℝ
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), proof of Theorem 8.1, uniform statement, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_c3

namespace GaussianSweep

/-- The uniform statement proved in the proof of Theorem 8.1 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), proof of Theorem 8.1, p.55
(PDF p.57)): for every `ε > 0` there is `N(ε)` such that every graph `G` with `Δ(G) ≤ 3` and
`n ≥ N(ε)` vertices satisfies `pw(G) ≤ (c₃ + ε)n`.

**Formalization Note** A graph is a `SimpleGraph` on a finite vertex type `V`, `n = card V`; it may
be disconnected and have vertices of degree 0, 1, 2. -/
theorem theorem_8_1_uniform : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (V : Type) [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 3 → N ≤ Fintype.card V →
      (pathwidth G : ℝ) ≤ (c3 + ε) * Fintype.card V := by sorry

end GaussianSweep
