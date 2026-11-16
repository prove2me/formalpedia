-- Prove2me | Theorems.Thm_GaussianSweep_Supplement_theorem_7_1
-- name    : GaussianSweep.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:40:45.609641+00:00
-- url     : https://prove2.me/theorems/4671beca-bf48-4125-b639-abd51ba380c0
-- title:
--   Theorem 7.1 — $\Delta \le 4$: $\mathrm{pw} \le a_3 n_3 + a_4 n_4 + o(n)$ for $(F_4,F_4)$, $(F_3, 0.2575)$, $(5/32, 1/4)$
-- statement:
--   Let $n_d$ be the number of vertices of degree $d$, and $F_3$, $F_4$ the suprema of the ideal 3- and 4-star functions (Definition 6.7). Every finite simple graph $G$ with $\Delta(G) \le 4$ satisfies
--   $$
--   \mathrm{pw}(G) \le a_3 n_3 + a_4 n_4 + o(n)
--   $$
--   for each of the pairs
--
--   1. $(a_3,a_4) = (F_4, F_4)$, and in particular $\mathrm{pw}(G) \le F_4 n + o(n)$;
--   2. $(a_3,a_4) = (F_3, 0.2575)$;
--   3. $(a_3,a_4) = (5/32, 1/4)$.
--
--   Each bound has its own remainder, a function of $n$ alone. Part 1 is Theorem 1.1(b) of the paper.
--
--   Differences from the source:
--   - encoding: o(n) for each of the pairs, and in the 'in particular' clause → a separate ∃ ρ with ρ(n)/n → 0, before the graph, for each of the four bounds; reason: the paper's remainder convention (p.1); the maximum of finitely many o(n) functions is o(n), so one or several remainders say the same
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 7.1, p.38 (PDF p.40); Theorem 1.1(b), p.1 (PDF p.3)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_Supplement_numDeg
import Definitions.Def_GaussianSweep_Supplement_F3
import Definitions.Def_GaussianSweep_Supplement_F4__069df8
open Filter Topology

namespace GaussianSweep.Supplement

/-- Theorem 7.1 (maximum degree 4) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 7.1, p.38 (PDF p.40);
part (a) is Theorem 1.1(b), p.1 (PDF p.3)). Every graph `G` with `Δ(G) ≤ 4` satisfies
`pw(G) ≤ a₃ n₃ + a₄ n₄ + o(n)` for each of the pairs
(a) `(a₃, a₄) = (F₄, F₄)`, and in particular `pw(G) ≤ F₄ n + o(n)`;
(b) `(a₃, a₄) = (F₃, 0.2575)`;
(c) `(a₃, a₄) = (5/32, 1/4)`.

**Formalization Note** `n_d` is the number of vertices of degree exactly `d` (`numDeg`);
vertices of degree `≤ 2` contribute nothing. `F₃`, `F₄` are the suprema of Definition 6.7, not
numerical enclosures; `0.2575` is the exact rational. Each of the four bounds has its own
remainder `ρ : ℕ → ℝ` with `ρ(n)/n → 0`, chosen before the graph. -/
theorem theorem_7_1 :
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 4 →
        (GaussianSweep.pathwidth G : ℝ) ≤
          F4 * numDeg G 3 + F4 * numDeg G 4 + ρ (Fintype.card V)) ∧
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 4 →
        (GaussianSweep.pathwidth G : ℝ) ≤ F4 * Fintype.card V + ρ (Fintype.card V)) ∧
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 4 →
        (GaussianSweep.pathwidth G : ℝ) ≤
          F3 * numDeg G 3 + 0.2575 * numDeg G 4 + ρ (Fintype.card V)) ∧
    (∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 4 →
        (GaussianSweep.pathwidth G : ℝ) ≤
          5 / 32 * numDeg G 3 + 1 / 4 * numDeg G 4 + ρ (Fintype.card V)) := by sorry

end GaussianSweep.Supplement
