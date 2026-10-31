-- Prove2me | Theorems.Thm_MultimodularDocks_lemma_3_4
-- name    : MultimodularDocks.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:39.50631+00:00
-- url     : https://prove2.me/theorems/21008fc4-800d-412e-8682-338c4501bb3f
-- title:
--   Lemma 3.4 (corrected: the step is Algorithm 2's output) — after a gradient step from an optimum of $S_r$, no improving neighbor in $S_{r+1}$
-- statement:
--   Let every station cost be multimodular and let $a_0$ be a feasible initial allocation. Let $x$ minimize the objective among the feasible allocations at dock-move distance at most $r$ from $a_0$, and let $y$ be the output of the gradient-descent step (Algorithm 2) applied to $x$. Then no feasible allocation in $N(y)$ (the result of any dock-move $o_{ij},e_{ij},E_{ijh},O_{ijh}$ applied to $y$, with $i,j,h$ unrestricted) at dock-move distance at most $r+1$ from $a_0$ has a smaller objective than $y$:
--
--   $$
--   w\in N(y),\ w \text{ feasible},\ \tfrac12|\vec d_w+\vec b_w-\vec d_{a_0}-\vec b_{a_0}|_1\le r+1\ \Longrightarrow\ c(y)\le c(w).
--   $$
--
--   Local optimality in the next ball is the first half of the induction behind Theorem 1; by itself it does not give optimality in the ball (Remark, p.20).
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - encoding: dock-move distance |d + b − d' − b'|₁ / 2 ≤ r → dockGap ≤ 2 * r with dockGap = Σ_i |(d_i + b_i) − (d'_i + b'_i)|; reason: avoids division; same relation
--   - reading: N(d, b) with i, j, h ∈ [n] unrestricted (p.18), in the step of Algorithm 2 → IsGDStep uses Neighbor (a dock-move with i ≠ j, h free); the conclusion ranges over every m.apply y, i, j, h unrestricted; reason: the page states that every neighbor is at |d + b − d' − b'|₁ = 2, which needs i ≠ j; x minimizes over S_r, which contains every reallocation of its bikes, so x is bike-optimal and the moves with i = j (bike moves or the identity) never improve it: the step from x is the same under both readings (paper.md item 5)
--   - correction: Lemma 3.4 (p.20): 'the next choice of the gradient-descent algorithm, i.e., an allocation in the neighborhood of (d^r, b^r) that minimizes the objective' → y is the output of Algorithm 2 from x (IsGDStep): the best feasible neighbor if it is strictly better, else x itself; reason: the 'i.e.' is false when no neighbor improves: two stations, g(d, b) = (d + b − 1)², l = 0, u = 2, B = 0, D = 2, r = 0, x = (d = (1, 1)) of cost 0; its best neighbor (2, 0) costs 2, and x is a neighbor of it in S_1 with a lower objective (paper.md item 2)
--   - reading: ball |d + b − d^r − b^r|₁ ≤ 2r, with the bold (d, b) both the initial allocation and the bound variable (p.20) → the ball is centered at the initial allocation a₀: dockGap z a₀ ≤ 2 * r; reason: the paragraph above the lemma ('at dock-move distance at most r to (d⁰, b⁰)') and S_r(d, b) on p.49 fix the center (paper.md item 3)
--   - reading: initial allocation (d̄, b̄) with l_i ≤ d̄_i + b̄_i ≤ u_i and |d̄ + b̄|₁ = D + B (p.11) → a₀ is P3-feasible, including |b̄|₁ = B; reason: only the dock counts of a₀ enter the statement, and whenever a feasible x exists (0 ≤ B ≤ D + B) the docks of a₀ can be split to hold B bikes, so the condition excludes no ball (paper.md item 6)
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Lemma 3.4, p.20; proof App. C.3, pp.49–53

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsGDStep
import Definitions.Def_MultimodularDocks_dockGap

namespace MultimodularDocks

/-- **Lemma 3.4** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Lemma 3.4, p.20; proof
App. C.3, pp.49–53). Let every station cost be multimodular and `a₀` a feasible initial
allocation. Let `x` minimize the objective among feasible allocations at dock-move distance at
most `r` from `a₀`, and let `y` be the next choice of the gradient-descent step (Algorithm 2)
from `x`. Then no feasible allocation in `N(y)` (the result `m.apply y` of any dock-move `m`)
at dock-move distance at most `r + 1` from `a₀` has a smaller objective than `y`.

**Formalization Note** The ball is centered at the initial allocation `a₀` (the page's bold
`(d⃗, b⃗)`; p.20, "at dock-move distance at most r to (d⃗0, b⃗0)", and `S_r(d⃗, b⃗)`, p.49).
"The next choice of the gradient-descent algorithm" is the output of Algorithm 2; the page's
gloss "an allocation in the neighborhood … that minimizes the objective" is false when no
neighbor improves (then Algorithm 2 stays at `x`). The conclusion is over the page's `N(y)`
with `i, j, h` unrestricted, so it also covers the bike moves from `y` (`i = j`); the step
`IsGDStep` uses `Neighbor` (`i ≠ j`), which gives the same steps from `x`, since `x` is
bike-optimal. -/
theorem lemma_3_4 {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a₀ : Alloc S) (ha₀ : Feasible I a₀) (r : ℕ)
    (x y : Alloc S) (hx : Feasible I x) (hxr : dockGap x a₀ ≤ 2 * (r : ℤ))
    (hxmin : ∀ z, Feasible I z → dockGap z a₀ ≤ 2 * (r : ℤ) → cost I x ≤ cost I z)
    (hstep : IsGDStep I x y) :
    ∀ m : DockMove S, Feasible I (m.apply y) → dockGap (m.apply y) a₀ ≤ 2 * ((r : ℤ) + 1) →
      cost I y ≤ cost I (m.apply y) := by sorry

end MultimodularDocks
