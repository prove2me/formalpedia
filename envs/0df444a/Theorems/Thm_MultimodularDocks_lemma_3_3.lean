-- Prove2me | Theorems.Thm_MultimodularDocks_lemma_3_3
-- name    : MultimodularDocks.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:30.79752+00:00
-- url     : https://prove2.me/theorems/d377031d-0bb9-4cf2-9518-0ea889e3488b
-- title:
--   Lemma 3.3 (corrected: Definition 1 on the quadrant) — the exchange lemma for bike-optimal allocations
-- statement:
--   Let every station cost be multimodular, let $(\vec d,\vec b)$ be bike-optimal, and let $(\vec d^\star,\vec b^\star)$ be a feasible allocation with a smaller objective. Let $j$ and $k$ be stations with
--
--   $$
--   d_j+b_j<d^\star_j+b^\star_j,\qquad d_k+b_k>d^\star_k+b^\star_k .
--   $$
--
--   Then there is a dock-move $m$ between two different stations, either with destination $j$ or with source $k$, such that $(\vec d',\vec b')=m(\vec d,\vec b)$ and $(\vec d^{\star\star},\vec b^{\star\star})=m^{-1}(\vec d^\star,\vec b^\star)$ are both feasible and
--
--   1. $c(\vec d,\vec b)-c(\vec d',\vec b')\ge c(\vec d^{\star\star},\vec b^{\star\star})-c(\vec d^\star,\vec b^\star)$;
--   2. $(\vec d',\vec b')$ is at smaller dock-move distance to $(\vec d^\star,\vec b^\star)$ than $(\vec d,\vec b)$ is, and $(\vec d^{\star\star},\vec b^{\star\star})$ is at smaller dock-move distance to $(\vec d,\vec b)$ than $(\vec d^\star,\vec b^\star)$ is;
--   3. the dock-move $m$ applied to $(\vec d^{\star\star},\vec b^{\star\star})$ yields $(\vec d^\star,\vec b^\star)$.
--
--   With destination $j$, station $j$ gains a dock in $(\vec d',\vec b')$ and loses one in $(\vec d^{\star\star},\vec b^{\star\star})$; with source $k$, the reverse holds at $k$. This exchange property drives both the optimality for (P3) and the proof of Theorem 1.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - encoding: dock-move distance |d + b − d' − b'|₁ / 2 ≤ r → dockGap ≤ 2 * r with dockGap = Σ_i |(d_i + b_i) − (d'_i + b'_i)|; reason: avoids division; same relation
--   - reading: N(d, b) with i, j, h ∈ [n] unrestricted (p.18) → Neighbor: a dock-move from i to j with i ≠ j, h free; reason: the page states that every neighbor is at |d + b − d' − b'|₁ = 2, which needs i ≠ j; for i = j the move is a bike move or the identity, which never improves a bike-optimal allocation, so no run changes (paper.md item 5)
--   - reading: 'a better allocation / solution' (d⋆, b⋆) → a P3-feasible allocation a' with cost a' < cost a; reason: the allocations compared are the feasible ones, with finite objective (paper.md item 7); equal bike totals are what excludes Cases 3.c) and 4.c) (p.46)
--   - reading: (d', b') ∈ N(d, b) and (d⋆⋆, b⋆⋆) ∈ N(d⋆, b⋆), with c possibly +∞ → both allocations are feasible (finite objective); reason: item 1 compares objective values and is only meaningful for finite ones; the page's construction moves docks toward the other allocation, which stays in the bands (the stronger reading)
--   - encoding: 'there exist (d′, b′) ∈ N(d, b) with d′_j + b′_j = d_j + b_j + 1 and (d⋆⋆, b⋆⋆) ∈ N(d⋆, b⋆) with d⋆⋆_j + b⋆⋆_j = d⋆_j + b⋆_j − 1', or the same at k with signs reversed → one dock-move m with m.src ≠ m.dst and (m.dst = j ∨ m.src = k), (d′, b′) = m.apply a and (d⋆⋆, b⋆⋆) = m.inv.apply a′; reason: item 3 says the two allocations are related by one dock-move and its inverse; the dock counts at j (resp. k) then change as printed
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Lemma 3.3, p.19; proof App. C.2.1, pp.45–48

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsBikeOptimal
import Definitions.Def_MultimodularDocks_DockMove
import Definitions.Def_MultimodularDocks_dockGap

namespace MultimodularDocks

/-- **Lemma 3.3** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Lemma 3.3, p.19; proof
App. C.2.1, pp.45–48). Let every station cost be multimodular, `a` bike-optimal and `a'` a
better feasible allocation. Let `j` and `k` be stations with fewer, resp. more, docks in `a`
than in `a'`. Then there is a dock-move `m` from a station to a different one, either into `j`
or out of `k`, such that both `m.apply a` and `m.inv.apply a'` are feasible and
1. `c(a) − c(m.apply a) ≥ c(m.inv.apply a') − c(a')`;
2. `m.apply a` is at smaller dock-move distance to `a'` than `a` is, and `m.inv.apply a'` is at
   smaller dock-move distance to `a` than `a'` is;
3. `m` applied to `m.inv.apply a'` yields `a'`.

**Formalization Note** `(d⃗′, b⃗′) = m.apply a` and `(d⃗⋆⋆, b⃗⋆⋆) = m.inv.apply a'`. The page's
two alternatives are `m.dst = j` (then `d′_j + b′_j = d_j + b_j + 1` and
`d⋆⋆_j + b⋆⋆_j = d⋆_j + b⋆_j − 1`) and `m.src = k`. The page writes `∈ N(·)` for an objective
that is `+∞` off the band; feasibility of both allocations is stated, since item 1 is about
finite objective values. -/
theorem lemma_3_3 {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a a' : Alloc S) (ha : IsBikeOptimal I a)
    (ha' : Feasible I a') (hlt : cost I a' < cost I a) (j k : S)
    (hj : dockCount a j < dockCount a' j) (hk : dockCount a' k < dockCount a k) :
    ∃ m : DockMove S, m.src ≠ m.dst ∧ (m.dst = j ∨ m.src = k) ∧
      Feasible I (m.apply a) ∧ Feasible I (m.inv.apply a') ∧
      cost I (m.inv.apply a') - cost I a' ≤ cost I a - cost I (m.apply a) ∧
      dockGap (m.apply a) a' < dockGap a a' ∧ dockGap (m.inv.apply a') a < dockGap a' a ∧
      m.apply (m.inv.apply a') = a' := by sorry

end MultimodularDocks
