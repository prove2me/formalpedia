-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_best_sample_point
-- name    : LubyMIS.Derandomized.best_sample_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:59:55.287904+00:00
-- url     : https://prove2.me/theorems/16932baa-17d9-4a2e-8824-e726e5f347fb
-- title:
--   Some sample point (x, y) eliminates at least 1/18 of the edges
-- statement:
--   Let $G'$ be a graph on the vertices $\{0, \dots, n-1\}$ in which every vertex has degree $d(i) < n/16$, and let $q$ be a prime with $n \le q \le 2n$. For a sample point $(x, y)$, $0 \le x, y \le q-1$, set $\mathrm{coin}(i) = 1$ iff $(x + y\cdot i) \bmod q < \lfloor q/2d(i) \rfloor$, and let $I'$ be Algorithm B's selection for these coins. Then there is a sample point $(x,y)$ for which
--   $$|E'| \ \le\ 18 \cdot \bigl|\{\text{edges of } G' \text{ with an endpoint in } I' \cup N(I')\}\bigr| .$$
--
--   Consequently the sample point that Algorithm D selects, one maximizing the number of eliminated edges, eliminates at least $1/18$ of the edges of $G'$.
--
--   **Formalization Note** The coin rule is the one of the definition of Algorithm D, with the strict test $l(i) < n(i)$ in place of the printed $l(i) \le n(i)$ (see that definition).
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1047, §4.4, paragraph on Algorithm D ("Theorem 3 shows that the best set will eliminate at least 1/18 of the edges")

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic
import Definitions.Def_LubyMIS_Derandomized_AlgorithmD

namespace LubyMIS.Derandomized

/-- The best sample point (Luby 1986, §4.4, p. 1047): if every vertex of the current graph `H` on
`Fin n` has `d(i) < n/16` and `q` is a prime with `n ≤ q ≤ 2n`, some sample point `(x, y)` of the
§4.2 space, used for Algorithm D's coins, eliminates at least `1/18` of the edges of `H`. -/
theorem best_sample_point (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (q : ℕ)
    (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (hdeg : ∀ i, 16 * H.degree i < n) :
    ∃ x y : ZMod q, (H.edgeFinset.card : ℝ) ≤ 18 * (eliminated H (selectB H (coinD q H x y)) : ℝ) := by sorry

end LubyMIS.Derandomized
