-- Prove2me | Theorems.Thm_LostSalesBalancing_DualBalancing_lemma_3_6
-- name    : LostSalesBalancing.DualBalancing.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:46.021165+00:00
-- url     : https://prove2.me/theorems/6d98cb38-1aae-4086-b2eb-bd249691ccfb
-- title:
--   Lemma 3.6 — lost-sales cost conditioned on the crossing event
-- statement:
--   Let the demands $D_1,\ldots,D_T\ge0$ have finite means, and let the information $\mathcal F_j$ available at the beginning of each period $j$ be independent of the future demands $(D_j,\ldots,D_T)$. Let $B$ be a dual-balancing policy and $P$ any feasible nonanticipatory comparison policy. For each $t\in[1,T-L]$, with $A_t=\{t\in\mathcal T_\Pi\}$,
--
--   $$
--   E[\mathbf1_{A_t}\mid\mathcal F_t]E[\Pi_t^B\mid\mathcal F_t]\le E[\mathbf1_{A_t}\Pi_t^B\mid\mathcal F_t]\quad\text{almost surely}.
--   $$
--
--   The inequality is the lost-sales counterpart of Lemma 3.5 and controls the other part of the marked cost comparison.
--
--   **Formalization Note** $\mathcal T_\Pi$ is the complement of $\mathcal T_H$ within the order periods. The paper assumes independent demands; because its information set may include extra observations, the formalization explicitly requires each $\mathcal F_j$ independent of future demands. Writing the conditional event expression as an indicator product avoids dividing by zero. Marginal cost integrability comes from the dual-balancing predicate.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript p. 16, §3.2, Lemma 3.6

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model

namespace LostSalesBalancing.DualBalancing

open Finset MeasureTheory ProbabilityTheory
open LeviBalancing.DualBalancing

/-- Lemma 3.6 in conditional-expectation form, on the complementary event `T_Π`. -/
theorem lemma_3_6 {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℤ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : LSInstance) (DP : DemandProcess ℱ μ I.T)
    (hD : IndependentDemands I ℱ μ DP) (B P : ℤ → Ω → ℝ)
    (hB : IsDualBalancingLS I ℱ μ DP.D B)
    (hP : IsFeasiblePolicy I.toInstance ℱ P)
    (t : ℤ) (ht : 1 ≤ t) (hT : t ≤ (I.T : ℤ) - I.L) :
    (fun ω => (μ[((setTH I DP.D B P t)ᶜ).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω *
      (μ[randLostLS I DP.D B t | ℱ t]) ω) ≤ᵐ[μ]
      μ[((setTH I DP.D B P t)ᶜ).indicator (randLostLS I DP.D B t) | ℱ t] := by sorry

end LostSalesBalancing.DualBalancing
