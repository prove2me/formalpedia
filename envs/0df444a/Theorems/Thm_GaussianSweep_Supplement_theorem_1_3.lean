-- Prove2me | Theorems.Thm_GaussianSweep_Supplement_theorem_1_3
-- name    : GaussianSweep.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:38:38.527508+00:00
-- url     : https://prove2.me/theorems/8cdb0a3a-389f-4711-8caf-c10a9fb0dabd
-- title:
--   Theorem 1.3 — all graphs: $\mathrm{pw}(G) \le \sum_{d\ge3} a_d n_d + o(n)$ with closed-form $a_d$
-- statement:
--   Every finite simple graph $G$ satisfies
--   $$
--   \mathrm{pw}(G) \le \sum_{d \ge 3} a_d\, n_d + o(n),
--   $$
--   where $n_d$ is the number of vertices of degree $d$ and
--   $$
--   a_d = \begin{cases} \dfrac{3d-4}{32} & 3 \le d \le 6,\\[4pt] 1 - \dfrac{111}{28(d+1)} & 7 \le d \le 10,\\[4pt] 1 - \dfrac{4}{d+1} & d \ge 11. \end{cases}
--   $$
--   The remainder $o(n)$ is one function of $n$ alone, the same for all graphs. The first coefficients are $(a_3,a_4,a_5,a_6) = (5/32, 1/4, 11/32, 7/16)$. No degree bound is assumed.
--
--   This is the paper's per-vertex bound for graphs with vertices of all degrees.
--
--   Differences from the source:
--   - encoding: o(n): a function of n alone, the same for all graphs in the class (p.1) → ∃ ρ : ℕ → ℝ with ρ(n)/n → 0, quantified before the vertex type and the graph; reason: the paper's stated remainder convention (Section 1.1, p.1); the published goal uses the same encoding
--   - encoding: Σ_{d≥3} a_d n_d → Σ over 3 ≤ d ≤ n of a_d · n_d; reason: every degree is at most n − 1, so n_d = 0 for d ≥ n and the two sums are equal
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 1.3, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_Supplement_numDeg
open Filter Topology

namespace GaussianSweep.Supplement

/-- Theorem 1.3 (all graphs) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 1.3, p.2 (PDF p.4)). Every
graph `G` satisfies `pw(G) ≤ Σ_{d≥3} a_d n_d + o(n)` for the sequence
`a_d = (3d − 4)/32` for `3 ≤ d ≤ 6`, `a_d = 1 − 111/(28(d + 1))` for `7 ≤ d ≤ 10`, and
`a_d = 1 − 4/(d + 1)` for `d ≥ 11`.

**Formalization Note** Every finite simple graph on any finite vertex type, no degree bound.
`n_d` is the number of vertices of degree exactly `d`; the sum `Σ_{d≥3}` is written over
`3 ≤ d ≤ n`, which loses nothing since `n_d = 0` for `d ≥ n`. The coefficient is the closed
form by range of `d` (the `if` branches are only evaluated at `d ≥ 3`). One remainder
`ρ : ℕ → ℝ` with `ρ(n)/n → 0`, chosen before the graph. -/
theorem theorem_1_3 : ∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (GaussianSweep.pathwidth G : ℝ) ≤
        (∑ d ∈ Finset.Icc 3 (Fintype.card V),
          (if d ≤ 6 then (3 * (d : ℝ) - 4) / 32
           else if d ≤ 10 then 1 - 111 / (28 * ((d : ℝ) + 1))
           else 1 - 4 / ((d : ℝ) + 1)) * (numDeg G d : ℝ)) + ρ (Fintype.card V) := by sorry

end GaussianSweep.Supplement
