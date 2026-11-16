-- Prove2me | Theorems.Thm_GaussianSweep_Supplement_theorem_7_2
-- name    : GaussianSweep.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:41:28.260006+00:00
-- url     : https://prove2.me/theorems/e9960b7b-4ead-45ae-a7c5-205f57d4cbee
-- title:
--   Theorem 7.2 — $\Delta \le 5$: $\mathrm{pw} \le a_3 n_3 + a_4 n_4 + a_5 n_5 + o(n)$ for the triples P, R, S
-- statement:
--   Let $n_d$ be the number of vertices of degree $d$ and $F_3$ the supremum of the ideal 3-star function (Definition 6.7). Every finite simple graph $G$ with $\Delta(G) \le 5$ satisfies
--   $$
--   \mathrm{pw}(G) \le a_3 n_3 + a_4 n_4 + a_5 n_5 + o(n)
--   $$
--   for each of the triples
--
--   - P: $(a_3,a_4,a_5) = (F_3,\ 0.2575,\ 0.3667)$;
--   - R: $(a_3,a_4,a_5) = (0.1455,\ 0.2530,\ 0.3600)$;
--   - S: $(a_3,a_4,a_5) = (5/32,\ 1/4,\ 11/32)$.
--
--   Each triple has its own remainder, a function of $n$ alone. The decimals are exact.
--
--   Differences from the source:
--   - encoding: o(n) for each of the triples → a separate ∃ ρ with ρ(n)/n → 0, before the graph, for each triple; reason: the paper's remainder convention (p.1)
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 7.2, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_Supplement_numDeg
import Definitions.Def_GaussianSweep_Supplement_F3
open Filter Topology

namespace GaussianSweep.Supplement

/-- Theorem 7.2 (maximum degree 5) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 7.2, p.38 (PDF p.40)).
Every graph `G` with `Δ(G) ≤ 5` satisfies `pw(G) ≤ a₃ n₃ + a₄ n₄ + a₅ n₅ + o(n)` for each of the
triples
P `(a₃, a₄, a₅) = (F₃, 0.2575, 0.3667)`;
R `(a₃, a₄, a₅) = (0.1455, 0.2530, 0.3600)`;
S `(a₃, a₄, a₅) = (5/32, 1/4, 11/32)`.

**Formalization Note** `n_d` is the number of vertices of degree exactly `d` (`numDeg`);
vertices of degree `≤ 2` contribute nothing. `F₃` is the supremum of Definition 6.7; the
decimals are exact rationals. Each triple has its own remainder `ρ : ℕ → ℝ` with `ρ(n)/n → 0`,
chosen before the graph. -/
theorem theorem_7_2 :
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 5 →
        (GaussianSweep.pathwidth G : ℝ) ≤
          F3 * numDeg G 3 + 0.2575 * numDeg G 4 + 0.3667 * numDeg G 5 + ρ (Fintype.card V)) ∧
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 5 →
        (GaussianSweep.pathwidth G : ℝ) ≤
          0.1455 * numDeg G 3 + 0.2530 * numDeg G 4 + 0.3600 * numDeg G 5 +
            ρ (Fintype.card V)) ∧
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 5 →
        (GaussianSweep.pathwidth G : ℝ) ≤
          5 / 32 * numDeg G 3 + 1 / 4 * numDeg G 4 + 11 / 32 * numDeg G 5 +
            ρ (Fintype.card V)) := by sorry

end GaussianSweep.Supplement
