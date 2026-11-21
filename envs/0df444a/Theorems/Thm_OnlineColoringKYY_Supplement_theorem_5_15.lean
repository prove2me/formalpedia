-- Prove2me | Theorems.Thm_OnlineColoringKYY_Supplement_theorem_5_15
-- name    : OnlineColoringKYY.Supplement.theorem_5_15
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T07:10:54.089351+00:00
-- url     : https://prove2.me/theorems/68239085-f454-49ba-a1ea-f7456d79d444
-- title:
--   Theorem 5.15 — Algorithm 2 uses $n/d + 11d\,n^{(2d-4)/(2d-3)}k^{(d-1)/(2d-3)}$ colors in expectation
-- statement:
--   Let $d \ge 2$ be an integer and consider Algorithm 2, the $d$-level randomized online coloring algorithm, with integer thresholds $\theta_{d-1}, \dots, \theta_1 \ge 1$. For all integers $n, k \ge 0$ there are thresholds $\theta_1, \dots, \theta_{d-1} \ge 1$, depending only on $d$, $n$ and $k$, such that for every $k$-colorable graph $G$ on $n$ vertices, presented in a fixed arrival order, the expected number of colors Algorithm 2 uses is
--   $$
--   \mathbb E\bigl[\,|\{c(v) : v \in V(G)\}|\,\bigr] \;\le\; \frac nd + 11\,d\; n^{\frac{2d-4}{2d-3}}\; k^{\frac{d-1}{2d-3}},
--   $$
--   the expectation being over the algorithm's random choices only (oblivious adversary).
--
--   With $d$ of order $\log n/\log\log n$ this gives the randomized algorithms for graphs of large chromatic number behind Theorem 1.2.
--
--   Differences from the source:
--   - encoding: n-vertex k-colorable graph, parameters θ_{d−1}, …, θ_1 chosen with n and k known in advance → G : SimpleGraph (Fin n) with arrival order 0, …, n−1 and G.Colorable k; θ : ℕ → ℕ with θ i ≥ 1 for 1 ≤ i ≤ d − 1, chosen before G; colors in ℕ, fresh color = 1 + largest used color; expectation as a sum in ℝ≥0∞ bounded by ENNReal.ofReal of the real bound, exponents as real powers; reason: Lean conventions; the same instances and the same quantity
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Theorem 5.15, printed p.21 (PDF p.23); Algorithm 2, printed pp.17–18 (PDF pp.19–20)

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common
import Definitions.Def_OnlineColoringKYY_Supplement_dLevel

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

/-- **Theorem 5.15** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios
Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256
3d1eeea6…), printed p.21 = PDF p.23). Let `d ≥ 2` be an integer. Algorithm 2 uses at most
`n/d + 11 d n^{(2d−4)/(2d−3)} k^{(d−1)/(2d−3)}` colors in expectation for an `n`-vertex
`k`-colorable graph, when `n` and `k` are known in advance, with an appropriate setting of the
parameters `θ_{d−1}, …, θ_2, θ_1`.

**Formalization Note** The thresholds `θ 1, …, θ (d − 1)` are positive integers depending on
`d`, `n`, `k` only, chosen before the input graph (oblivious adversary). The bound holds for every
`k`-colorable graph on `Fin n` (arrival order `0, 1, …, n − 1`). The expectation is over the
algorithm's coins only, computed in `ℝ≥0∞`. The exponents are real powers. -/
theorem theorem_5_15 (d : ℕ) (hd : 2 ≤ d) :
    ∀ n k : ℕ, ∃ θ : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) ∧
      ∀ (G : SimpleGraph (Fin n)), G.Colorable k →
        expColors (dLevelRun d θ G n le_rfl) ≤
          ENNReal.ofReal ((n : ℝ) / (d : ℝ) + 11 * (d : ℝ) *
            (n : ℝ) ^ ((2 * (d : ℝ) - 4) / (2 * (d : ℝ) - 3)) *
            (k : ℝ) ^(((d : ℝ) - 1) / (2 * (d : ℝ) - 3))) := by sorry

end OnlineColoringKYY.Supplement
