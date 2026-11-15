-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1IdleRegulatorIdentity
-- name    : Kyprianou.Ch01.mg1IdleRegulatorIdentity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:24:12.659623+00:00
-- url     : https://prove2.me/theorems/0e75bb84-12d4-4489-89d6-7feaacd3c402
-- title:
--   Exercise 1.9(iii): M/G/1 idle-time regulator equals reflected process running maximum
-- statement:
--   Exercise 1.9(iii) proves the Skorokhod reflection regulator identity for the M/G/1 workload path W: total idle time accumulated up to t is max(sup_{0≤s≤t} X_s−w,0), where X_s=s−Σ_{i≤N_s} ξ_i and W_t=max(w,sup X_s)−X_t. For independent positive jobs the equality holds almost surely simultaneously for all t. The identity is an intermediate proof obligation for Theorem 1.11, not an assumption of the desired idle-time law. Draft awaits remote Lean elaboration.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(iii), printed p. 31.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mg1IdleRegulatorIdentity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPositiveClaims : F (Set.Iic (0 : ℝ)) = 0) :
    ∀ w : ℝ, 0 ≤ w →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        (∫ s in (0 : ℝ)..(t : ℝ),
          (if queueWorkload arrival claims w (Real.toNNReal s) ω = 0
            then (1 : ℝ) else 0) ∂volume) =
        max
          ((sSup {x : ℝ | ∃ s : ℝ≥0,
            s ≤ t ∧
              x = riskSurplus arrival claims 1 0 s ω}) - w) 0 := by
  sorry
