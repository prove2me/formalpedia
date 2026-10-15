-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_11
-- name    : OnlineMaxWeightMatch.Approx.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:05.25879+00:00
-- url     : https://prove2.me/theorems/6fcf3666-86a0-4b4c-be1e-2e8d51461b98
-- title:
--   Lemma 4.11: Pr[O_{i,t} | A_t, i1 ≠ i, U1(t)] ≤ Pr[O_{i,t}] · (1 + 12c/(1/2 − c)^2)
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   Let $O_{i,t}$ be the event that bin $i$ is occupied at time $t$, $A_t$ the event that ball $t$ arrives, $i_1$ the bin picked in Line 5 at time $t$, and $U_1(t)$ the event that $t$ is unmatched after its first pick. For every late edge $(i,t)$,
--
--   $$
--   \Pr\big[O_{i,t}\ \big|\ A_t,\ i_1\neq i,\ U_1(t)\big]\ \le\ \Pr[O_{i,t}]\cdot\Big(1+\frac{12c}{(1/2-c)^2}\Big).
--   $$
--
--   Conditioning on the ball's arrival, on a first pick other than $i$ and on the first pick's failure changes the occupancy probability of $i$ only by a small factor; this is the input to the proof of Theorem 4.6.
--
--   **Formalization Note** The condition is the intersection $A_t\cap\{i_1\neq i\}\cap U_1(t)$, via `ProbabilityTheory.cond`. If that event has probability $0$ (e.g. $p_t=0$), Lean's conditional probability is $0$ and the inequality holds trivially; the paper's statement is then undefined.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 16, Lemma 4.11

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Lemma 4.11. For any late edge `(i, t)`,
`Pr[O_{i,t} | A_t, i_1 ≠ i, U_1(t)] ≤ Pr[O_{i,t}] · (1 + 12c/(1/2 - c)^2)`. -/
theorem lemma_4_11 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (i : ι) (t : Fin n) (hlate : IsLate x i t) :
    (algMeasure I x)[|arrivalSet t ∩ (firstPickSet t i)ᶜ ∩ unmatchedAfterFirstSet x t].real
        (occupiedSet x i t) ≤
      (algMeasure I x).real (occupiedSet x i t) * (1 + 12 * c / (1 / 2 - c) ^ 2) := by sorry

end OnlineMaxWeightMatch.Approx
