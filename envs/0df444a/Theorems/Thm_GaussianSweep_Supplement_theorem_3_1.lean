-- Prove2me | Theorems.Thm_GaussianSweep_Supplement_theorem_3_1
-- name    : GaussianSweep.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:39:14.057749+00:00
-- url     : https://prove2.me/theorems/c4be43b9-82b4-45d5-b66c-3eff318fca3b
-- title:
--   Theorem 3.1 — cut sweep: $\mathrm{pw}(G) \le \mathrm{cw}(G) \le \frac{3}{2\pi}\arcsin\frac13\, n + o(n)$ for $\Delta \le 3$
-- statement:
--   Every finite simple graph $G$ with maximum degree $\Delta(G) \le 3$ satisfies
--   $$
--   \mathrm{pw}(G) \le \mathrm{cw}(G) \le c^* n + o(n), \qquad c^* = \frac{3}{2\pi}\arcsin\frac13 \approx 0.16226,
--   $$
--   where the $o(n)$ is one function of $n$ alone, the same for all such graphs. Both inequalities are asserted; the first holds exactly.
--
--   This is the short-proof bound below $n/6$ for the pathwidth and cutwidth of graphs of maximum degree $3$.
--
--   Differences from the source:
--   - encoding: o(n): a function of n alone, the same for all graphs in the class (p.1) → ∃ ρ : ℕ → ℝ with ρ(n)/n → 0, quantified before the vertex type and the graph; reason: the paper's stated remainder convention (Section 1.1, p.1); the published goal uses the same encoding
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 3.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_Supplement_cutwidth
import Definitions.Def_GaussianSweep_Supplement_cStar
open Filter Topology

namespace GaussianSweep.Supplement

/-- Theorem 3.1 (cut sweep) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 3.1, p.14 (PDF p.16)). Every
graph `G` with `Δ(G) ≤ 3` satisfies `pw(G) ≤ cw(G) ≤ c* n + o(n)`, where
`c* = (3/(2π)) arcsin(1/3)`.

**Formalization Note** Both inequalities are stated: `pw(G) ≤ cw(G)` exactly, and
`cw(G) ≤ c* n + ρ(n)` with one function `ρ : ℕ → ℝ`, `ρ(n)/n → 0`, chosen before the graph
(the p.1 convention). A graph is a `SimpleGraph` on any finite vertex type, `n = |V|`;
disconnected graphs and vertices of any degree `≤ 3` are allowed. -/
theorem theorem_3_1 : ∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 3 →
      GaussianSweep.pathwidth G ≤ (cutwidth G : ℤ) ∧
        (cutwidth G : ℝ) ≤ cStar * Fintype.card V + ρ (Fintype.card V) := by sorry

end GaussianSweep.Supplement
