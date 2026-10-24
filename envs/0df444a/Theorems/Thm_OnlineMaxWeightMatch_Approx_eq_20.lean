-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_eq_20
-- name    : OnlineMaxWeightMatch.Approx.eq_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:47.333921+00:00
-- url     : https://prove2.me/theorems/3d640a34-b2fd-4ac5-b3d4-4be7ee22b2fd
-- title:
--   §4.3, Equation (20): Pr[U1(t) | A_t, i1 = j] ≥ 1/2 − c
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   Let $A_t$ be the event that ball $t$ arrives, $i_1$ the bin picked in Line 5 at time $t$, and $U_1(t)$ the event that $t$ is unmatched after its first pick. For every bin $j$ and ball $t$ with $x_{j,t}>0$,
--
--   $$
--   \Pr\big[U_1(t)\ \big|\ A_t,\ i_1=j\big]\ \ge\ 1/2-c. \tag{20}
--   $$
--
--   That is, whatever bin is picked first, the ball survives its first pick with probability at least $1/2-c$. The bound is used in Lemma 4.11 and in the proof of Theorem 4.6.
--
--   **Formalization Note** The hypothesis $x_{j,t}>0$ (which forces $p_t>0$) makes the conditioning event have positive probability; on a null event Lean's conditional measure is $0$ and the inequality would fail for a trivial reason. The conditional probability is `ProbabilityTheory.cond` on the intersection $A_t\cap\{i_1=j\}$.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 13, §4.3, Equation (20)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- §4.3, Equation (20). For every bin `j` and ball `t` with `x_{j,t} > 0` (so that the
conditioning event has positive probability), `Pr[U_1(t) | A_t, i_1 = j] ≥ 1/2 - c`. -/
theorem eq_20 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (j : ι) (t : Fin n) (hpos : 0 < x j t) :
    1 / 2 - c ≤ (algMeasure I x)[|arrivalSet t ∩ firstPickSet t j].real
      (unmatchedAfterFirstSet x t) := by sorry

end OnlineMaxWeightMatch.Approx
