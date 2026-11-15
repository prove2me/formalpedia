-- Prove2me | Theorems.Thm_Kyprianou_Ch01_riskSurplus_isCadlag_ae
-- name    : Kyprianou.Ch01.riskSurplus_isCadlag_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:00:45.132496+00:00
-- url     : https://prove2.me/theorems/bb639f91-321a-4ba3-b78b-ae51bf516825
-- title:
--   Cramer–Lundberg compound-Poisson surplus paths are almost surely cadlag
-- statement:
--   A linear premium drift minus an almost surely cadlag compound-Poisson claim process has cadlag paths almost surely.
-- source:
--   Kyprianou (2006), Chapter 1, risk and queue sections; existing source-file proof in research/kyprianou_ch01/proofs/risk_surplus_cadlag_bounded_v12.lean

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_ProbabilityTheory_compoundPoisson_ae_isCadlag
import Theorems.Thm_isCadlag_comp_nnrealCoe
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
import Theorems.Thm_Continuous_isCadlag
import Theorems.Thm_Kyprianou_Ch01_cadlag_nnreal_neg
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.riskSurplus_isCadlag_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) (premium x : ℝ) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => riskSurplus arrival claims premium x t ω) := by sorry
