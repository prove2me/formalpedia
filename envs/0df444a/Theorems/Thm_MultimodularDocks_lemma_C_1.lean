-- Prove2me | Theorems.Thm_MultimodularDocks_lemma_C_1
-- name    : MultimodularDocks.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:24.148505+00:00
-- url     : https://prove2.me/theorems/9a6ec815-beb0-44cf-9e3a-a92ed75ad050
-- title:
--   Lemma C.1 (corrected: Definition 1 on the quadrant) — structure of a better allocation in $S_{r+1}$
-- statement:
--   Let every station cost be multimodular, $a_0$ a feasible initial allocation, $x$ a minimizer of the objective among feasible allocations at dock-move distance at most $r$ from $a_0$, and $y$ the gradient-descent step from $x$, as in Lemma 3.4. Suppose a feasible $s$ at dock-move distance at most $r+1$ from $a_0$ has $c(s)<c(y)$. Writing $n_i(\cdot)$ for the number of docks at station $i$, there are stations $j,k$ with
--
--   $$
--   n_j(s)>n_j(x)\ge n_j(a_0),\qquad n_k(s)<n_k(x)\le n_k(a_0).
--   $$
--
--   The lemma is a step of the proof by contradiction of Theorem 1, which shows that no such $s$ exists; its hypotheses can therefore never all hold, exactly as on the page.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - encoding: dock-move distance |d + b − d' − b'|₁ / 2 ≤ r → dockGap ≤ 2 * r with dockGap = Σ_i |(d_i + b_i) − (d'_i + b'_i)|; reason: avoids division; same relation
--   - reading: N(d, b) with i, j, h ∈ [n] unrestricted (p.18) → Neighbor: a dock-move from i to j with i ≠ j, h free; reason: the page states that every neighbor is at |d + b − d' − b'|₁ = 2, which needs i ≠ j; for i = j the move is a bike move or the identity, which never improves a bike-optimal allocation, so no run changes (paper.md item 5)
--   - correction: Lemma 3.4 (p.20): 'the next choice of the gradient-descent algorithm, i.e., an allocation in the neighborhood of (d^r, b^r) that minimizes the objective' → y is the output of Algorithm 2 from x (IsGDStep): the best feasible neighbor if it is strictly better, else x itself; reason: the 'i.e.' is false when no neighbor improves: two stations, g(d, b) = (d + b − 1)², l = 0, u = 2, B = 0, D = 2, r = 0, x = (d = (1, 1)) of cost 0; its best neighbor (2, 0) costs 2, and x is a neighbor of it in S_1 with a lower objective (paper.md item 2)
--   - reading: ball |d + b − d^r − b^r|₁ ≤ 2r, with the bold (d, b) both the initial allocation and the bound variable (p.20) → the ball is centered at the initial allocation a₀: dockGap z a₀ ≤ 2 * r; reason: the paragraph above the lemma ('at dock-move distance at most r to (d⁰, b⁰)') and S_r(d, b) on p.49 fix the center (paper.md item 3)
--   - reading: initial allocation (d̄, b̄) with l_i ≤ d̄_i + b̄_i ≤ u_i and |d̄ + b̄|₁ = D + B (p.11) → a₀ is P3-feasible, including |b̄|₁ = B; reason: only the dock counts of a₀ enter the statement, and whenever a feasible x exists (0 ≤ B ≤ D + B) the docks of a₀ can be split to hold B bikes, so the condition excludes no ball (paper.md item 6)
--   - reading: (d⋆, b⋆) ∈ S_{r+1}(d, b) with c(d⋆, b⋆) < c(d^{r+1}, b^{r+1}) → s is feasible, dockGap s a₀ ≤ 2(r + 1), cost s < cost y; reason: a smaller objective than a finite one is finite, i.e. s is feasible (paper.md item 7)
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Lemma C.1, p.53

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsGDStep
import Definitions.Def_MultimodularDocks_dockGap

namespace MultimodularDocks

/-- **Lemma C.1** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Lemma C.1, p.53). Let every
station cost be multimodular, `a₀` feasible, `x` a minimizer of the objective among feasible
allocations at dock-move distance at most `r` from `a₀`, and `y` the gradient-descent step
from `x`, as in Lemma 3.4. If a feasible `s` at dock-move distance at most `r + 1` from `a₀`
has a smaller objective than `y`, then there are stations `j, k` with
`s_j > x_j ≥ a₀_j` and `s_k < x_k ≤ a₀_k`, where `·_i` is the number of docks at `i`.

**Formalization Note** This is a step of the proof by contradiction of Theorem 1: by that
theorem no such `s` exists, so the hypotheses cannot all hold. It is stated as on the page. -/
theorem lemma_C_1 {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a₀ : Alloc S) (ha₀ : Feasible I a₀) (r : ℕ)
    (x y : Alloc S) (hx : Feasible I x) (hxr : dockGap x a₀ ≤ 2 * (r : ℤ))
    (hxmin : ∀ z, Feasible I z → dockGap z a₀ ≤ 2 * (r : ℤ) → cost I x ≤ cost I z)
    (hstep : IsGDStep I x y) (s : Alloc S) (hs : Feasible I s)
    (hsr : dockGap s a₀ ≤ 2 * ((r : ℤ) + 1)) (hlt : cost I s < cost I y) :
    ∃ j k, dockCount x j < dockCount s j ∧ dockCount a₀ j ≤ dockCount x j ∧
      dockCount s k < dockCount x k ∧ dockCount x k ≤ dockCount a₀ k := by sorry

end MultimodularDocks
