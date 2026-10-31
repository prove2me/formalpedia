-- Prove2me | Theorems.Thm_MultimodularDocks_theorem_1
-- name    : MultimodularDocks.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:58.033713+00:00
-- url     : https://prove2.me/theorems/5e8335cc-b9b1-467e-8917-5270cb3231b7
-- title:
--   Theorem 1 (corrected: Definition 1 on the quadrant) — Algorithm 3 finds in iteration $r$ the best allocation within dock-move distance $r$
-- statement:
--   Let $S$ be a finite set of stations whose costs $c_i$ are all multimodular, with station bounds $l_i\le d_i+b_i\le u_i$, bike budget $B$ and $D+B$ docks in total. Run Algorithm 3 from a feasible allocation $a_0=(\bar{\vec d},\bar{\vec b})$, with any tie-breaking, and let $x_0,x_1,x_2,\dots$ be its iterates. Then:
--
--   1. for every $r$, $x_r$ is feasible, at dock-move distance at most $r$ from $a_0$, and minimizes the objective among all feasible allocations at dock-move distance at most $r$ from $a_0$:
--
--   $$
--   c(x_r)=\min\Bigl\{c(\vec d,\vec b):\ (\vec d,\vec b)\ \text{feasible},\ \tfrac12|\vec d+\vec b-\bar{\vec d}-\bar{\vec b}|_1\le r\Bigr\};
--   $$
--
--   2. if the run is stationary at $r$ ($x_{r+1}=x_r$), then $x_r$ is optimal for (P3);
--   3. $x_{D+B}$ is optimal for (P3);
--   4. the run is constant from iteration $D+B$ on.
--
--   Clause 1 is Theorem 1. With $r=z$ it says that Algorithm 3 solves problem (P2) with operational constraint $z$, for every $z$ at once, and clauses 2–4 are the consequences stated in §3: a stationary point is optimal without operational constraint, and $D+B$ iterations suffice.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - generalization: Theorem 1: x_r minimizes the objective within dock-move distance r → adds clauses 2–4: a stationary iterate is P3-optimal, x_{D+B} is P3-optimal, the run is constant from D + B on; reason: these are the consequences stated in §3 (p.17, 'requires at most D + B iterations'), §3.2 (p.18) and §3.3 (p.20, min{D + B, z}); clause 1 is the printed theorem
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - encoding: dock-move distance |d + b − d' − b'|₁ / 2 ≤ r → dockGap ≤ 2 * r with dockGap = Σ_i |(d_i + b_i) − (d'_i + b'_i)|; reason: avoids division; same relation
--   - encoding: Algorithms 1–3 as procedures with arg max / arg min and a return statement → relations (IsBikeGreedyRun, IsGDStep, IsAlgorithm3Run) covering every tie-breaking; a stopped run is a constant sequence; reason: every execution of the pseudocode is a run of the relation and conversely; quantifying over all runs covers every tie-breaking
--   - reading: N(d, b) with i, j, h ∈ [n] unrestricted (p.18) → Neighbor: a dock-move from i to j with i ≠ j, h free; reason: the page states that every neighbor is at |d + b − d' − b'|₁ = 2, which needs i ≠ j; for i = j the move is a bike move or the identity, which never improves a bike-optimal allocation, so no run changes (paper.md item 5)
--   - reading: 'Initialized at (d, b)': the bold (d, b) of the theorem and of S_r(d, b) → the initial allocation a₀ = (d̄, b̄) of Algorithm 3, the center of every ball; reason: (d⁰, b⁰) has the same docks as (d̄, b̄), so S_r is the same for both (paper.md items 3, 4)
--   - reading: initial allocation with |d̄ + b̄|₁ = D + B and l_i ≤ d̄_i + b̄_i ≤ u_i (p.11) → a₀ is P3-feasible, including |b̄|₁ = B; reason: Algorithm 1 keeps |b|₁ fixed, so a start with |b̄|₁ ≠ B never becomes feasible (paper.md item 6)
--   - reading: 'allocations' compared in Theorem 1 → P3-feasible allocations; reason: those with finite objective (paper.md item 7)
--   - reading: 'iteration r' after Algorithm 3 has returned → x_r of the run, which is constant after a stationary step; reason: Algorithm 3 returns at the first stationary step, so its output for budget z is x_z (paper.md item 8)
--   - reading: §3: 'requires at most D + B iterations' → x_{(D+B).toNat} is P3-optimal and the run is constant from there; reason: any two P3-feasible allocations are within dock-move distance D + B; D + B ≥ 0 follows from the feasibility of a₀, so toNat loses nothing (paper.md item 11)
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Theorem 1, p.20; proof App. C.4, pp.53–54; §3 p.17, §3.2 p.18, §3.3 p.20

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsOptimalP3
import Definitions.Def_MultimodularDocks_IsAlgorithm3Run
import Definitions.Def_MultimodularDocks_dockGap

namespace MultimodularDocks

/-- **Theorem 1** (Freund, Henderson, Shmoys, *Minimizing Multimodular Functions and Allocating
Capacity in Bike-Sharing Systems*, arXiv:1611.09304v5, Theorem 1, p.20; proof App. C.4,
pp.53–54; with §3 p.17, §3.2 p.18 and §3.3 p.20). Let `S` be a finite set of stations whose
costs are all multimodular, and let Algorithm 3 run from a feasible allocation `a₀`, with any
tie-breaking. Then
1. for every `r`, the iterate `x r` is feasible, at dock-move distance at most `r` from `a₀`,
   and has the least objective among all feasible allocations at dock-move distance at most `r`
   from `a₀` (Theorem 1);
2. if the run is stationary at `r` (`x (r + 1) = x r`), then `x r` is optimal for (P3) (§3.2);
3. `x (D + B)` is optimal for (P3), and
4. the run is constant from iteration `D + B` on (§3, "requires at most D + B iterations").

**Formalization Note** Station costs are real functions multimodular on the quadrant, with the
band `l_i ≤ d + b ≤ u_i` in place of the value `+∞` (`Feasible`). Allocations are integer
vectors with explicit nonnegativity. "Dock-move distance at most `r`" is `dockGap ≤ 2 * r`. A
run is a relation (`IsAlgorithm3Run`), so every tie-breaking is covered, and a stopped run is
constant. Neighbors move a dock between distinct stations. `D + B ≥ 0` follows from the
feasibility of `a₀`, so `(D + B).toNat` loses nothing. -/
theorem theorem_1 {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a₀ : Alloc S) (ha₀ : Feasible I a₀)
    (x : ℕ → Alloc S) (hrun : IsAlgorithm3Run I a₀ x) :
    (∀ r : ℕ, Feasible I (x r) ∧ dockGap (x r) a₀ ≤ 2 * (r : ℤ) ∧
      ∀ y, Feasible I y → dockGap y a₀ ≤ 2 * (r : ℤ) → cost I (x r) ≤ cost I y) ∧
    (∀ r : ℕ, x (r + 1) = x r → IsOptimalP3 I (x r)) ∧
    IsOptimalP3 I (x (I.D + I.B).toNat) ∧
    (∀ r : ℕ, (I.D + I.B).toNat ≤ r → x r = x (I.D + I.B).toNat) := by sorry

end MultimodularDocks
