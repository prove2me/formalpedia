-- Prove2me | Theorems.Thm_MultimodularDocks_run_bike_optimal
-- name    : MultimodularDocks.run_bike_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:40.129527+00:00
-- url     : https://prove2.me/theorems/837d03a0-ef58-491b-b990-3c296ea922ca
-- title:
--   Implication 1 of Lemma 3.1 (corrected: Definition 1 on the quadrant) — every iterate of Algorithm 3 is bike-optimal
-- statement:
--   Let every station cost be multimodular and let $a_0$ be a feasible allocation. Then
--
--   1. Algorithm 3 started at $a_0$ has a run, and
--   2. along every run $x_0,x_1,x_2,\dots$ (any tie-breaking), every iterate $x_r$ is bike-optimal.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - encoding: Algorithms 1–3 as procedures with arg max / arg min and a return statement → relations (IsBikeGreedyRun, IsGDStep, IsAlgorithm3Run) covering every tie-breaking; a stopped run is a constant sequence; reason: every execution of the pseudocode is a run of the relation and conversely; quantifying over all runs covers every tie-breaking
--   - reading: implication 1 speaks of the iterates of Algorithm 3, presupposing that it runs → clause (i): a run exists; reason: the algorithm is well defined on feasible inputs (finitely many neighbors); stating it rules out a vacuous clause (ii)
--   - reading: initial allocation with |d̄ + b̄|₁ = D + B and l_i ≤ d̄_i + b̄_i ≤ u_i (p.11) → a₀ is P3-feasible, including |b̄|₁ = B; reason: Algorithm 1 keeps |b|₁ fixed, so a start with |b̄|₁ ≠ B never becomes feasible (paper.md item 6)
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Implication 1 of Lemma 3.1, p.19

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsBikeOptimal
import Definitions.Def_MultimodularDocks_IsAlgorithm3Run

namespace MultimodularDocks

/-- **Bike-optimality is an invariant of Algorithm 3** (Freund, Henderson, Shmoys,
arXiv:1611.09304v5, implication 1 of Lemma 3.1, p.19). If every station cost is multimodular
and the start `a₀` is feasible, then (i) Algorithm 3 has a run from `a₀`, and (ii) along every
run all iterates `x 0, x 1, x 2, …` are bike-optimal. -/
theorem run_bike_optimal {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a₀ : Alloc S) (ha₀ : Feasible I a₀) :
    (∃ x : ℕ → Alloc S, IsAlgorithm3Run I a₀ x) ∧
      ∀ x : ℕ → Alloc S, IsAlgorithm3Run I a₀ x → ∀ r, IsBikeOptimal I (x r) := by sorry

end MultimodularDocks
