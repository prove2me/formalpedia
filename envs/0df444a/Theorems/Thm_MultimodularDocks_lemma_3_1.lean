-- Prove2me | Theorems.Thm_MultimodularDocks_lemma_3_1
-- name    : MultimodularDocks.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:13.503986+00:00
-- url     : https://prove2.me/theorems/80ad1693-3c20-4963-ab16-fd254dbeab0c
-- title:
--   Lemma 3.1 (corrected: Definition 1 on the quadrant) — a best dock-move preserves bike-optimality
-- statement:
--   Let every station cost be multimodular and let $(\vec d,\vec b)$ be bike-optimal. Fix any stations $i$ and $j$ (also $i=j$) and let $m$ be a best dock-move from $i$ to $j$: the allocation $m(\vec d,\vec b)$ is feasible, and no feasible allocation obtained from $(\vec d,\vec b)$ by a dock-move from $i$ to $j$ (any of $o_{ij}$, $e_{ij}$, $E_{ijh}$, $O_{ijh}$) has a smaller objective. Then $m(\vec d,\vec b)$ is bike-optimal.
--
--   Consequently Algorithm 3 never has to re-optimize the bikes after a dock-move: every iterate stays bike-optimal.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - reading: 'the best dock-move from i to j' → every minimizer among the feasible dock-moves from i to j; reason: the stronger reading: the claim holds whichever minimizer is chosen
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Lemma 3.1, p.19; proof App. C.1, pp.44–45

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsBikeOptimal
import Definitions.Def_MultimodularDocks_DockMove

namespace MultimodularDocks

/-- **Lemma 3.1** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Lemma 3.1, p.19; proof
App. C.1, pp.44–45). Let every station cost be multimodular and let `a` be bike-optimal. For
any stations `i` and `j`, let `m` be a best dock-move from `i` to `j`: `m.apply a` is feasible and has
the least objective among all feasible results of dock-moves from `i` to `j`. Then `m.apply a`
is bike-optimal.

**Formalization Note** Every minimizer is covered, not only one. "Any i and j" includes
`i = j`: the dock-moves from `i` to `i` are the identity (`o i i`, `e i i`) and the bike moves
`E i i h`, `O i i h`, and the claim holds for them as well. -/
theorem lemma_3_1 {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a : Alloc S) (ha : IsBikeOptimal I a)
    (m : DockMove S) (hfeas : Feasible I (m.apply a))
    (hbest : ∀ m' : DockMove S, m'.src = m.src → m'.dst = m.dst → Feasible I (m'.apply a) →
      cost I (m.apply a) ≤ cost I (m'.apply a)) :
    IsBikeOptimal I (m.apply a) := by sorry

end MultimodularDocks
