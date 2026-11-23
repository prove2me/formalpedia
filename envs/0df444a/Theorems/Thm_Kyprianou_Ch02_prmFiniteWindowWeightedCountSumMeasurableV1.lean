-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowWeightedCountSumMeasurableV1
-- name    : Kyprianou.Ch02.prmFiniteWindowWeightedCountSumMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:22:32.27847+00:00
-- url     : https://prove2.me/theorems/e3b8a511-b4b7-4c03-b82c-049e3e271429
-- title:
--   Measurability of finite weighted Poisson marked-window cell sums
-- statement:
--   For a KLS Poisson random measure, fixed time window, measurable mark set, finitely many measurable mark cells and deterministic real weights, the finite weighted count sum is a measurable random variable. Direct consequence of PRM measurable_eval, ENNReal.measurable_toReal and Finset.measurable_sum. Reusable in the source-exact finite-simple marked-integral approximation for Chapter 2 independent increments and characteristic exponents.
-- source:
--   Kyprianou Chapter 2 finite-region Poisson marked integral and LevyStochCalc Poisson/CharacterCell.lean, verified original source measurable count cells.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteWindowWeightedCountSumMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i)) (w : Fin n → ℝ) :
    Measurable (fun (ω : Ω) =>
      ∑ i : Fin n, (w i) *
        (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) := by sorry
