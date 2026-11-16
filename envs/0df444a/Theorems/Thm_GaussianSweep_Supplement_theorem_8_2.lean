-- Prove2me | Theorems.Thm_GaussianSweep_Supplement_theorem_8_2
-- name    : GaussianSweep.Supplement.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:42:04.576357+00:00
-- url     : https://prove2.me/theorems/5ce14d3e-c7b9-4f34-8b2f-f1359ea8d644
-- title:
--   Theorem 8.2 — $\Delta \le 4$: $\mathrm{pw}(G) \le c_3 n_3 + 0.2627\, n_4 + o(n)$
-- statement:
--   Every finite simple graph $G$ with $\Delta(G) \le 4$ satisfies
--   $$
--   \mathrm{pw}(G) \le c_3\, n_3 + 0.2627\, n_4 + o(n), \qquad c_3 = \frac{3}{4\pi}\arccos\frac56,
--   $$
--   where $n_d$ is the number of vertices of degree $d$ and the $o(n)$ is one function of $n$ alone. It contains Theorem 8.1 (graphs with $\Delta \le 3$ have $n_4 = 0$ and $n_3 \le n$).
--
--   Differences from the source:
--   - encoding: o(n): a function of n alone, the same for all graphs in the class (p.1) → ∃ ρ : ℕ → ℝ with ρ(n)/n → 0, quantified before the vertex type and the graph; reason: the paper's stated remainder convention (Section 1.1, p.1); the published goal uses the same encoding
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 8.2, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_c3
import Definitions.Def_GaussianSweep_Supplement_numDeg
open Filter Topology

namespace GaussianSweep.Supplement

/-- Theorem 8.2 (maximum degree 4) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 8.2, p.45 (PDF p.47)).
Every graph `G` with `Δ(G) ≤ 4` satisfies `pw(G) ≤ c₃ n₃ + 0.2627 n₄ + o(n)`, where
`c₃ = (3/(4π)) arccos(5/6)`.

**Formalization Note** `c₃` is the published `GaussianSweep.c3`; `n_d` is the number of
vertices of degree exactly `d`; `0.2627` is the exact rational. One remainder `ρ : ℕ → ℝ` with
`ρ(n)/n → 0`, chosen before the graph. -/
theorem theorem_8_2 : ∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 4 →
      (GaussianSweep.pathwidth G : ℝ) ≤
        GaussianSweep.c3 * numDeg G 3 + 0.2627 * numDeg G 4 + ρ (Fintype.card V) := by sorry

end GaussianSweep.Supplement
