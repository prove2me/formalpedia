-- Prove2me | Theorems.Thm_LostSalesBalancing_DualBalancing_lemma_3_1
-- name    : LostSalesBalancing.DualBalancing.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:12.891704+00:00
-- url     : https://prove2.me/theorems/21a94a08-a4b6-445c-9678-366df5a97d92
-- title:
--   Lemma 3.1 — expected cost equals twice the balanced charges
-- statement:
--   Let $B$ be a feasible dual-balancing policy on a probability space. For each order period $t\le T-L$, let $Z_t=E[H_t^B\mid\mathcal F_t]=E[\Pi_t^B\mid\mathcal F_t]$ be its balanced conditional cost. Then
--
--   $$
--   E[C(B)]=2\sum_{t=1}^{T-L}E[Z_t].
--   $$
--
--   This identity converts the policy's total cost into the balanced charges used in the approximation bound.
--
--   **Formalization Note** Holding and lost-sales marginal costs are integrable in the dual-balancing predicate, so the conditional expectations are genuine. The expected cost and the expectations of nonnegative $Z_t$ are lower Lebesgue integrals in $[0,\infty]$. The probability space may be arbitrary.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript p. 7, §3.2, Lemma 3.1

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model

namespace LostSalesBalancing.DualBalancing

open Finset MeasureTheory
open scoped ENNReal

/-- Lemma 3.1: expected balancing cost is twice the sum of expected balanced charges. -/
theorem lemma_3_1 {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℤ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : LSInstance) (D B : ℤ → Ω → ℝ)
    (hB : IsDualBalancingLS I ℱ μ D B) :
    expectedCostLS I μ D B =
      2 * ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
        ∫⁻ ω, ENNReal.ofReal ((μ[randHoldingLS I D B t | ℱ t]) ω) ∂μ := by sorry

end LostSalesBalancing.DualBalancing
