-- Prove2me | Theorems.Thm_LostSalesBalancing_DualBalancing_lemma_3_5
-- name    : LostSalesBalancing.DualBalancing.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:18.155316+00:00
-- url     : https://prove2.me/theorems/d3b0052e-3db0-4632-8473-79b81a55fdbc
-- title:
--   Lemma 3.5 — holding cost conditioned on the all-lower event
-- statement:
--   Let the demands $D_1,\ldots,D_T\ge0$ have finite means, and let the information $\mathcal F_j$ available at the beginning of each period $j$ be independent of the future demands $(D_j,\ldots,D_T)$. Let $B$ be a dual-balancing policy and $P$ any feasible nonanticipatory comparison policy. For each $t\in[1,T-L]$, with $A_t=\{t\in\mathcal T_H\}$,
--
--   $$
--   E[\mathbf1_{A_t}\mid\mathcal F_t]E[H_t^B\mid\mathcal F_t]\le E[\mathbf1_{A_t}H_t^B\mid\mathcal F_t]\quad\text{almost surely}.
--   $$
--
--   Conditioning on the all-lower event cannot reduce the holding charge below its beginning-of-period conditional level, after weighting by the event probability.
--
--   **Formalization Note** The paper assumes independent demands; with an information set that may contain extra observations, the formalization requires $\mathcal F_j$ independent of the joint demand vector $D_j,\ldots,D_T$ at each $j$. The product form uses $E[\mathbf1_AH\mid\mathcal F]$ for conditional-on-an-event expectation, avoiding division by a zero conditional probability. The dual-balancing predicate supplies integrable marginal costs.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript pp. 15–16, §3.2, Lemma 3.5

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model

namespace LostSalesBalancing.DualBalancing

open Finset MeasureTheory ProbabilityTheory
open LeviBalancing.DualBalancing

/-- Lemma 3.5 in conditional-expectation form without division by a conditional event
probability: `E[1_A|F] E[H|F] ≤ E[1_A H|F]`. -/
theorem lemma_3_5 {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℤ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : LSInstance) (DP : DemandProcess ℱ μ I.T)
    (hD : IndependentDemands I ℱ μ DP) (B P : ℤ → Ω → ℝ)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P)
    (t : ℤ) (ht : 1 ≤ t) (hT : t ≤ (I.T : ℤ) - I.L) :
    (fun ω => (μ[(setTH I DP.D B P t).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω *
      (μ[randHoldingLS I DP.D B t | ℱ t]) ω) ≤ᵐ[μ]
      μ[(setTH I DP.D B P t).indicator (randHoldingLS I DP.D B t) | ℱ t] := by sorry

end LostSalesBalancing.DualBalancing
