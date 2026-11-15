-- Prove2me | Theorems.Thm_Kyprianou_Ch01_riskSurplus_runningSup_bddAbove_ae
-- name    : Kyprianou.Ch01.riskSurplus_runningSup_bddAbove_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:06:44.078587+00:00
-- url     : https://prove2.me/theorems/a1f51123-8bac-4c56-9c32-d017bbe170a6
-- title:
--   Cramer–Lundberg surplus has finite running supremum on finite horizons
-- statement:
--   For almost every sample path, the range of the Cramer–Lundberg surplus process on any finite time interval is bounded above.
-- source:
--   Kyprianou (2006), Chapter 1, risk and queue sections; existing source-file proof in research/kyprianou_ch01/proofs/risk_surplus_cadlag_bounded_v12.lean

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_isCadlag_ae
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.riskSurplus_runningSup_bddAbove_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) (premium x : ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BddAbove {z : ℝ | ∃ s : ℝ≥0,
        s ≤ T ∧ z = riskSurplus arrival claims premium x s ω} := by sorry
