-- Prove2me | Theorems.Thm_OnlineColoringKYY_theorem_1_1
-- name    : OnlineColoringKYY.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:38.071311+00:00
-- url     : https://prove2.me/theorems/f84b6c8e-df94-4e45-9752-83da5d91ea05
-- title:
--   Theorem 1.1 — every deterministic online coloring algorithm is $\Omega(n/\log n)$-competitive
-- statement:
--   There are constants $c > 0$ and $N$ such that for every $n \ge N$ and every proper deterministic online coloring algorithm $A$ there is a graph $G$ on exactly $n$ vertices, presented online, with
--   $$
--   \mathrm{ALG}_A(G) \;\ge\; c \cdot \frac{n}{\log_2 n} \cdot \chi(G).
--   $$
--   Equivalently, the competitive ratio $\max_I \mathrm{ALG}(I)/\mathrm{OPT}(I)$ of Definition 3.2 of every deterministic online coloring algorithm, over instances with $n$ vertices, is at least $c\, n/\log n$: **every deterministic online coloring algorithm is $\Omega(n/\log n)$-competitive.** The constant $c$ is the same for all algorithms, and the bound holds even if the algorithm knows $n$ in advance.
--
--   This is the paper's deterministic lower bound, the first improvement since Halldórsson and Szegedy (1994) over their $\Omega(n/\log^2 n)$. Together with the paper's randomized upper bound $O(n(\log\log n)^2/\log^2 n)$ (Theorem 1.2, not part of this mission), it shows that randomization helps in online graph coloring.
--
--   **Formalization Note** $\chi(G)$ enters through $k$-colorability: the statement asks for some $k$ with $G$ $k$-colorable and $\mathrm{ALG} \ge c\,(n/\log_2 n)\,k$, which is equivalent because $\chi(G)$ is the least such $k$.
--
--   Differences from the source:
--   - reading: every deterministic online coloring algorithm is Ω(n/log n)-competitive → ∃ c > 0, ∃ N, ∀ n ≥ N, ∀ proper A, ∃ an n-vertex instance with ALG ≥ c·(n/log n)·χ; reason: the competitive ratio max_I ALG(I)/OPT(I) (Definition 3.2) as a function of the number n of vertices; one constant for all algorithms
--   - reading: the bound holds even if the final number of vertices n is known (proof, p.14) → A is quantified after n; reason: an algorithm that knows n is a family n ↦ A_n of algorithms; ∀ n ∀ A covers every such family and is logically the same as ∀ A ∀ n, so no case is added or dropped
--   - encoding: OPT(I) = χ(G) → ∃ k, G.Colorable k ∧ c·(n/log n)·k ≤ ALG; reason: χ(G) is the least k with G k-colorable, so the two are equivalent; avoids the junk chromaticNumber.toNat
--   - encoding: log n (base 2 by the paper's convention, p.10) → Real.logb 2 n; reason: the paper's base; Real.logb 2 1 = 0 only at n = 1, absorbed by the threshold N
--   - encoding: vertices of the input arrive one by one → G : SimpleGraph (Fin n) with vertex i the (i+1)-st arrival; reason: any arrival order is a bijection with Fin n; same instances
--   - encoding: a deterministic online algorithm colors each arriving vertex immediately, seeing the graph so far → OnlineColoringAlg: the color of the newest vertex as a function of the prefix graph on Fin (m+1); properness on every input (IsProper); reason: the earlier colors of a deterministic algorithm are functions of the earlier prefixes, so this is exactly the class of deterministic online algorithms
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Theorem 1.1, printed p.3 (PDF p.5); restated with its proof in Section 4.3, printed p.14 (PDF p.16)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run
import Definitions.Def_OnlineColoringKYY_IsProper
import Definitions.Def_OnlineColoringKYY_numColors

set_option autoImplicit false

namespace OnlineColoringKYY

/-- **Theorem 1.1** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Theorem 1.1, printed p.3 = PDF p.5; restated with its proof in
Section 4.3, printed p.14 = PDF p.16). Every deterministic online coloring algorithm is
`Ω(n / log n)`-competitive.

In Lean: there are a constant `c > 0` and a threshold `N` such that for every `n ≥ N` and every
proper deterministic online coloring algorithm `A` there is a graph `G` on exactly `n` vertices
and a `k` with `G` `k`-colorable (so `χ(G) ≤ k`) on which `A` uses at least
`c · (n / log₂ n) · k` colors. Hence `ALG(G) / χ(G) ≥ c · n / log₂ n`, and the competitive ratio
`max_I ALG(I)/OPT(I)` of Definition 3.2 over `n`-vertex instances is at least `c · n / log₂ n`.

**Formalization Note** One constant for all algorithms (`c`, `N` before `A`). Vertex `i` of
`Fin n` is the `i`-th arrival; the algorithm sees only the prefix graph. `χ(G)` enters through
`SimpleGraph.Colorable k`, which is equivalent because `χ` is the least such `k`. The logarithm is
base 2 (the paper's convention, p.10); another base only changes `c`. `Real.logb 2 1 = 0` makes the
inequality trivial at `n = 1`, which the existential threshold `N` absorbs. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : OnlineColoringAlg, IsProper A →
      ∃ G : SimpleGraph (Fin n), ∃ k : ℕ, G.Colorable k ∧
        c * ((n : ℝ) / Real.logb 2 n) * (k : ℝ) ≤ (numColors A G : ℝ) := by sorry

end OnlineColoringKYY
