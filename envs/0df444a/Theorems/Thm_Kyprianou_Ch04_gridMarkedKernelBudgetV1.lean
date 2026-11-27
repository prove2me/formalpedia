-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridMarkedKernelBudgetV1
-- name    : Kyprianou.Ch04.gridMarkedKernelBudgetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:59:47.236139+00:00
-- url     : https://prove2.me/theorems/b529179c-91a3-501d-bfdb-da70d2f0b079
-- title:
--   gridMarkedKernelBudgetV1
-- statement:
--   gridMarkedKernelBudgetV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), predictable grid kernel

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_nestedGridKernelSquareV1
import Theorems.Thm_Kyprianou_Ch04_cutoffBandEnergiesV1
import Theorems.Thm_Kyprianou_Ch04_integratedKernelBudgetV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrate the uniform nested-band budget for arbitrary bounded time weights. -/

theorem Kyprianou.Ch04.gridMarkedKernelBudgetV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (U V : ℝ → Ω → ℝ) (S : Ω → ℝ)
    (hS : Integrable S P) (hSnn : ∀ᵐ w ∂P, 0 ≤ S w)
    (hLeft : ∀ᵐ w ∂P, ∀ s ∈ Ioc (0 : ℝ) (T : ℝ),
      |U s w| ≤ K ∧ |U s w - V s w| ≤ K * Real.sqrt (S w))
    (hEnergy : (∫ w, S w ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    (∫ w, ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ z,
      (z * ((if a < |z| ∧ |z| < 1 then U s w else 0) -
        (if b < |z| ∧ |z| < 1 then V s w else 0)))^2 ∂ν ∂volume ∂P) ≤
      (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  sorry
