-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_theorem_4_2
-- name    : OnlineMaxWeightMatch.Approx.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:49.746134+00:00
-- url     : https://prove2.me/theorems/2d97bb15-17fb-4a52-8a01-ac14ebbdf103
-- title:
--   Theorem 4.2: each edge is matched with probability ≥ x_{i,t} · (1/2 + c)
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   Every edge $(i,t)$ is matched by Algorithm 1 with probability at least
--
--   $$
--   \Pr[(i,t)\in M]\ \ge\ x_{i,t}\cdot(1/2+c),
--   $$
--
--   where $M=M_1\sqcup M_2$ is the output matching.
--
--   By linearity of expectation this per-edge guarantee turns any LP-Match solution into an online algorithm earning a $(1/2+c)$ fraction of the LP objective.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 11, Theorem 4.2

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Algorithm1

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Theorem 4.2. Each edge `(i, t)` is matched by Algorithm 1 with probability at least
`Pr[(i, t) ∈ M] ≥ x_{i,t} · (1/2 + c)`. -/
theorem theorem_4_2 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (i : ι) (t : Fin n) :
    x i t * (1 / 2 + c) ≤ (algMeasure I x).real {ω | (i, t) ∈ algMatching x ω} := by sorry

end OnlineMaxWeightMatch.Approx
