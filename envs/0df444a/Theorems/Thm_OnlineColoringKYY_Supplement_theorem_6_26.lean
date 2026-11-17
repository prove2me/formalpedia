-- Prove2me | Theorems.Thm_OnlineColoringKYY_Supplement_theorem_6_26
-- name    : OnlineColoringKYY.Supplement.theorem_6_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:11:39.936083+00:00
-- url     : https://prove2.me/theorems/366f972d-56cb-45e5-9f28-4e38cd046d87
-- title:
--   Theorem 6.26 — for large $N$, LOC$(M^2)$ uses at most $3N/M$ colors
-- statement:
--   Fix $0 < \varepsilon < 2$. For the number of vertices $N$, known in advance, let (logarithms to base 2)
--   $$
--   M = \bigl\lfloor (\log\log N)^{1-\varepsilon/2} \bigr\rfloor, \qquad L = \bigl\lfloor N^{1/M^{11}} \bigr\rfloor .
--   $$
--   There is $N_0 = N_0(\varepsilon)$ such that for every $N \ge N_0$ the deterministic algorithm for LOC$(M^2)$ of Sections 6.5–6.8 (LOC, LOC$'$ and Algorithm 5, CB$(k,M,\nu)$, Algorithm 6, with the clique-free subroutine of Algorithms 3–4 and Corollary 6.5), run on any graph with at most $N$ vertices, uses at most
--   $$
--   \frac{3N}{M}
--   $$
--   colors, counting every vertex it colors, up to and including the vertex at which it terminates with a certificate, if it does. The bound holds for every way of making the choices the algorithm leaves arbitrary.
--
--   Since every $M^2$-colorable graph is locally $M^2$-colorable, the algorithm never terminates on an $M^2$-colorable graph, and so it colors $N$-vertex $M^2$-colorable graphs online with $O(N/M)$ colors; this is the main step towards the deterministic $O(n/(\log\log n)^{2-\varepsilon})$-competitive algorithm of Theorem 1.3.
--
--   Differences from the source:
--   - reading: assuming N is sufficiently large → ∃ N₀ (depending on ε), ∀ N ≥ N₀; reason: the usual meaning; ε ∈ (0, 2) is fixed first (p.22)
--   - reading: the choices the paper leaves arbitrary ("choose any such c" in Algorithm 3, "such a clique" in Section 6.6, adj(v) in Section 6.7, the instance I_{i,j} in Algorithm 6 line 5) → the bound holds for every valid resolver R of these choices, quantified after the input graph; reason: the proof uses no particular choice; quantifying over all of them is the stronger reading and covers every online rule
--   - reading: LOC(M²) on N vertices → every graph G on Fin n with n ≤ N (arrival order 0, …, n−1), locally M²-colorable or not; colors counted up to and including the vertex at which LOC(M²) terminates with a certificate, if it does; reason: LOC(M²) is a problem on every graph (Definition 6.7), it colors the last vertex even when it terminates, and fewer than N vertices is the same as N vertices with the rest unseen
--   - encoding: "we use disjoint colors for different bins / instances" → a color is a pair (address of the issuing instance, local color), with distinct addresses for distinct instances; the number of colors is the cardinality of the set of colors used; reason: realizes disjoint palettes; the count does not depend on how colors are named
--   - encoding: M = ⌊(log log N)^{1−ε/2}⌋, L = ⌊N^{1/M^{11}}⌋, log base 2, bound 3N/M → locM ε N = ⌊(logb 2 (logb 2 N))^(1 − ε/2)⌋₊, locL = ⌊N^(1/M^11)⌋₊, bound 3·N/M in ℝ; the recursion has fixed values on branches that cannot arise when M ≥ 1; reason: Lean conventions; M ≥ 1 for all large N, so the junk branches do not affect the statement
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Theorem 6.26, printed p.38 (PDF p.40); parameters p.22 (PDF p.24); algorithm in Sections 6.1–6.8, printed pp.22–35 (PDF pp.24–37)

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common
import Definitions.Def_OnlineColoringKYY_Supplement_cliqueFree
import Definitions.Def_OnlineColoringKYY_Supplement_locAlg

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

/-- **Theorem 6.26** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios
Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256
3d1eeea6…), printed p.38 = PDF p.40). Assuming `N` is sufficiently large, LOC(M²) uses at most
`3N/M` colors, where `M = ⌊(log log N)^{1−ε/2}⌋`, `L = ⌊N^{1/M^{11}}⌋` (p.22) for the fixed
`ε ∈ (0, 2)`.

**Formalization Note** "Sufficiently large" is `∃ N₀, ∀ N ≥ N₀` with `N₀` depending on `ε`. The
algorithm is `locRun`: Sections 6.5–6.8 (Algorithms 3–6, Corollary 6.5) with the parameters of
`N`, run on any graph with at most `N` vertices (the algorithm does not know the actual number
`n ≤ N`). Colors are counted up to and including the vertex at which LOC(M²) terminates with a
certificate, if it does. The bound holds for every valid resolution `R` of the choices the paper
leaves arbitrary, and on every input graph, locally `M²`-colorable or not. Logarithms are to base
2; `3N/M` is real division. -/
theorem theorem_6_26 (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, n ≤ N → ∀ (G : SimpleGraph (Fin n)),
      ∀ R : Resolver, R.Valid →
        ((locNumColors ε N R G : ℕ) : ℝ) ≤ 3 * (N : ℝ) / ((locM ε N : ℕ) : ℝ) := by sorry

end OnlineColoringKYY.Supplement
