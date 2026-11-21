-- Prove2me | Theorems.Thm_OnlineColoringKYY_Supplement_theorem_5_5
-- name    : OnlineColoringKYY.Supplement.theorem_5_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T07:10:14.665784+00:00
-- url     : https://prove2.me/theorems/c09401ea-cad8-4082-a499-5f2a2314400d
-- title:
--   Theorem 5.5 — the three-level algorithm uses $n/3 + O(n^{2/3}k^{2/3})$ colors in expectation
-- statement:
--   Consider the three-level randomized online coloring algorithm of Section 5.3 with integer threshold $\theta \ge 1$. There is an absolute constant $C > 0$ such that for all integers $n, k \ge 0$ there is a threshold $\theta = \theta(n, k) \ge 1$ with the following property: for every graph $G$ on $n$ vertices that is $k$-colorable, presented in a fixed arrival order, and for every rule choosing the eligible level-2 color in step 1, the expected number of colors used is
--   $$
--   \mathbb E\bigl[\,|\{c(v) : v \in V(G)\}|\,\bigr] \;\le\; \frac n3 + C\, n^{2/3} k^{2/3},
--   $$
--   where the expectation is over the algorithm's random choices only (oblivious adversary).
--
--   In particular the algorithm uses $(1+o(1))\,n/3$ colors in expectation when $k = o(\sqrt n)$, beating the $n/2$ barrier of every deterministic algorithm on such graphs (Theorem 1.1's construction).
--
--   Differences from the source:
--   - reading: n/3 + O(n^{2/3}k^{2/3}) colors in expectation → one absolute constant C > 0, chosen before n and k, with E[#colors] ≤ n/3 + C·n^{2/3}·k^{2/3} for all n, k; reason: the O(·) is uniform in n and k (the proof gives (enk)^{2/3} + 2/3 at real θ); this is the stronger reading
--   - reading: "If there is an eligible level-2 color, we assign this color" (which one is not said) → the bound holds for every rule sel that returns an eligible level-2 color, the rule being quantified after the input graph; reason: the paper leaves the choice open; quantifying over all rules is the stronger reading and covers every fixed rule
--   - encoding: n-vertex k-colorable graph, arrival order, colors, θ chosen with n and k known in advance → G : SimpleGraph (Fin n) with arrival order 0, …, n−1 and G.Colorable k; colors in ℕ, fresh color = 1 + largest used color; θ ≥ 1 chosen before G; expectation over the coins as a sum in ℝ≥0∞ bounded by ENNReal.ofReal of the real bound; reason: Lean conventions; the same instances and the same quantity
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Theorem 5.5, printed p.17 (PDF p.19); algorithm in Section 5.3, printed p.15 (PDF p.17)

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common
import Definitions.Def_OnlineColoringKYY_Supplement_threeLevel

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

/-- **Theorem 5.5** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios
Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256
3d1eeea6…), printed p.17 = PDF p.19). The three-level algorithm of Section 5.3 uses at most
`n/3 + O(n^{2/3} k^{2/3})` colors in expectation, when `n` and `k` are known in advance, with an
appropriate setting of the parameter `θ`.

**Formalization Note** The `O(·)` is one absolute constant `C`, chosen before `n` and `k`. The
threshold `θ ≥ 1` may depend on `n` and `k` only, and is chosen before the input graph
(oblivious adversary). The bound holds for every `n`-vertex `k`-colorable graph `G` on `Fin n`
(arrival order `0, 1, …, n − 1`) and every rule `sel` choosing the eligible level-2 color of
step 1. The expectation is over the algorithm's coins only, computed in `ℝ≥0∞`. Exponents `2/3` are
real powers. -/
theorem theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (G : SimpleGraph (Fin n)), G.Colorable k →
      ∀ sel : List ℕ → Finset ℕ → ℕ, (∀ c S, S.Nonempty → sel c S ∈ S) →
        expColors (threeLevelRun θ sel G n le_rfl) ≤
          ENNReal.ofReal ((n : ℝ) / 3 + C * (n : ℝ) ^ ((2 : ℝ) / 3) * (k : ℝ) ^ ((2 : ℝ) / 3)) := by sorry

end OnlineColoringKYY.Supplement
