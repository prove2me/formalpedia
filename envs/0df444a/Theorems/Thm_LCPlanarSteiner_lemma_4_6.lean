-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_4_6
-- name    : LCPlanarSteiner.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:34.267572+00:00
-- url     : https://prove2.me/theorems/87052ad7-cfec-4ab8-b540-a7ff330ded47
-- title:
--   Lemma 4.6 — searchable density: a junction of density $\le 19968D_r^4X/\varepsilon$ with pair paths $\le (1+\varepsilon)h$
-- statement:
--   Let $G$ be a planar graph with nonnegative costs and lengths, $h > 0$, $0 < \varepsilon \le 1$, and $(s_i, t_i)$, $i \in [r]$, $r \ge 1$, nonself pairs of vertices. Let $(x, y, f)$ be a feasible point of the density LP (15) at a root $v$, of value $X = \sum_e c_e x_e$.
--
--   **Lemma 4.6 (Searchable density).** In time polynomial in the binary input and $1/\varepsilon$ one can compute a nonempty original junction $(H', v, I)$ with
--   $$
--   \frac{c(H')}{|I|} \le \frac{19968\, D_r^4\, X}{\varepsilon},
--   $$
--   such that every $i \in I$ has $\mathrm{dist}_{H'}(s_i, v) + \mathrm{dist}_{H'}(v, t_i) \le (1+\varepsilon)h$ and a complete original simple pair path from $s_i$ to $t_i$ inside $H'$ of length at most $(1 + \varepsilon)h$, which is returned.
--
--   Repeating this search over all roots and removing the served pairs is the algorithm of Theorem 1.2.
--
--   Differences from the source:
--   - reading: yields, in polynomial time → one function computed by a Turing machine in time polynomial in the length of the binary LP point padded by ⌈1/ε⌉ symbols; reason: the paper names no machine model; the proof's rooted calls run in time polynomial in the inverse accuracy 1/σ ≤ 3/ε
--   - generalization: a nonempty original junction with complete original pair lengths at most (1 + ε)h → a junction (H′, v, I) at the given root v with arm sums ≤ (1 + ε)h, and for each listed pair a simple path from s_i to t_i inside H′ of length ≤ (1 + ε)h; reason: (17) bounds the concatenated arms through v by (1 + ε)h, and cycle erasure gives the simple pair path; both are given by the proof
--   - encoding: a feasible point of value X; planar G → an LP point given as finite lists, checked by LPFeasible, X = Σ_e c_e x_e; planarity of the input graph; divisions cleared; reason: Lean convention; G is planar throughout the paper (p.2)
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.6 and its proof, p.15

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_ArmsLE
import Definitions.Def_LCPlanarSteiner_Dlog
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_LPFeasible
import Definitions.Def_LCPlanarSteiner_LPPoint
import Definitions.Def_LCPlanarSteiner_encLPIn
import Definitions.Def_LCPlanarSteiner_encJunctionOut
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner

/-- **Lemma 4.6 (Searchable density).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.6, p.15: "A feasible point of value X yields, in polynomial time, a nonempty original
junction of density at most 19968D_r⁴X/ε, with complete original pair lengths at most (1 + ε)h."
Proof, p.15: "reverse its incoming path on the original labels and concatenate through the same
root v. Its total length is at most m_i + E + (U − m_i) + E = U + 2E = (1 + ε)h. (17) Cycle erasure
gives an original simple pair path."

There is a function `alg`, computable by a Turing machine in time polynomial in the length of
`encLPIn P` (the binary LP point padded by `⌈1/ε⌉` symbols), mapping an LP point to
`(H′, I, paths)`, such that for every well-formed planar graph, `h > 0`, `0 < ε ≤ 1`, `r ≥ 1` nonself
pairs of vertices and every feasible point `(x, y, f)` of the LP at the root `v`, with value `X`:
`I` is a nonempty list of distinct pair indices, `c(H′)/|I| ≤ 19968 D_r⁴ X/ε`, and for each listed
pair `i`, `dist_{H′}(s_i, v) + dist_{H′}(v, t_i) ≤ (1 + ε)h` and the corresponding output path is a
simple path from `s_i` to `t_i` inside `H′` of length `≤ (1 + ε)h`.

**Formalization Note.** The junction is `(H′, v, I)` with the given root `v`. Planarity of `G` is the
setting of §4 (the proof applies (7) in `G` and in its reverse). The time is polynomial in the
binary input and `1/ε` (padding). The division is cleared: `c(H′) · ε ≤ 19968 D_r⁴ X |I|`. -/
theorem lemma_4_6 :
    ∃ alg : LPPoint → List ℕ × List ℕ × List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encLPIn encJunctionOut alg) ∧
      ∀ P : LPPoint, P.net.WF →
        RobertsonSeymour1986.GM5.IsPlanar (underlying P.net P.net.allArcs) →
        0 < P.h → 0 < P.ε → P.ε ≤ 1 → P.dem ≠ [] →
        (∀ d ∈ P.dem, d.1 < P.net.n ∧ d.2 < P.net.n) → (∀ d ∈ P.dem, d.1 ≠ d.2) →
        LPFeasible P.net P.dem P.root P.ε P.h P.fx P.fy P.ff →
        (alg P).2.1 ≠ [] ∧ (alg P).2.1.Nodup ∧ (∀ i ∈ (alg P).2.1, i < P.dem.length) ∧
        (alg P).2.2.length = (alg P).2.1.length ∧
        pcost P.net (alg P).1.toFinset * P.ε ≤
          19968 * (Dlog P.dem.length : ℚ) ^ 4 * lpValue P.net P.fx * (alg P).2.1.length ∧
        ∀ k < (alg P).2.1.length,
          ArmsLE P.net (alg P).1.toFinset P.root
            (P.dem.getD ((alg P).2.1.getD k 0) (0, 0)).1
            (P.dem.getD ((alg P).2.1.getD k 0) (0, 0)).2 ((1 + P.ε) * P.h) ∧
          IsSPath P.net (P.dem.getD ((alg P).2.1.getD k 0) (0, 0)).1
            (P.dem.getD ((alg P).2.1.getD k 0) (0, 0)).2 ((alg P).2.2.getD k []) ∧
          (∀ e ∈ (alg P).2.2.getD k [], e ∈ (alg P).1) ∧
          plen P.net ((alg P).2.2.getD k []) ≤ (1 + P.ε) * P.h := by sorry

end LCPlanarSteiner
