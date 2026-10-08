-- Prove2me | Theorems.Thm_LeviBalancing_DualBalancing_expected_cost_eq_two_sum_balanced
-- name    : LeviBalancing.DualBalancing.expected_cost_eq_two_sum_balanced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:37:18.477562+00:00
-- url     : https://prove2.me/theorems/c35ebada-5c2b-4c42-96ec-7231aa205b03
-- title:
--   Lemma 4.1, p. 294 — $E[\mathcal C(B)] = 2\sum_{t=1}^{T-L} E[Z_t]$
-- statement:
--   Let $B$ be a dual-balancing policy for an instance with horizon $T$ and lead time $L$, under a demand process on a probability space with filtration $(\mathcal F_t)$. For $t = 1, \dots, T - L$ let
--   $$Z_t = E\bigl[H^B_t \mid \mathcal F_t\bigr] \;(= E[\Pi^B_t \mid \mathcal F_t] \text{ a.s.})$$
--   be the balanced cost of period $t$. Then the expected cost of $B$ is twice the expected sum of the balanced costs:
--   $$E[\mathcal C(B)] = 2 \sum_{t=1}^{T-L} E[Z_t].$$
--
--   This is the first half of the amortization in the proof of Theorem 4.1: the cost of the dual-balancing policy is expressed through the quantities $Z_t$, which the comparison with an arbitrary policy then bounds.
--
--   **Formalization Note** Both sides are in $[0,\infty]$: $E[\mathcal C(B)]$ is the lower Lebesgue integral of the realized cost, and $E[Z_t]$ is the lower Lebesgue integral of the positive part of a version of the conditional expectation (which is almost surely nonnegative).
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 294 (PDF p. 11), Lemma 4.1

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
import Definitions.Def_LeviBalancing_DualBalancing_Policy
open Finset MeasureTheory
open scoped ENNReal

namespace LeviBalancing.DualBalancing

/-- Lemma 4.1, p. 294: the expected cost of a dual-balancing policy is twice the expected sum of
the balanced costs `Z_t = E[H_t^B | ℱ t] = E[Π_t^B | ℱ t]`, `t = 1, …, T − L`. -/
theorem expected_cost_eq_two_sum_balanced {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℤ m} (I : Instance) (dem : DemandProcess ℱ μ I.T)
    (B : ℤ → Ω → ℝ) (hB : IsDualBalancing I ℱ μ dem.D B) :
    expectedCost I μ dem.D B =
      2 * ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
        ∫⁻ ω, ENNReal.ofReal ((μ[randHolding I dem.D B t | ℱ t]) ω) ∂μ := by sorry

end LeviBalancing.DualBalancing
