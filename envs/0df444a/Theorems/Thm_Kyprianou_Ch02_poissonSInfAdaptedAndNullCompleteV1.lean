-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonSInfAdaptedAndNullCompleteV1
-- name    : Kyprianou.Ch02.poissonSInfAdaptedAndNullCompleteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:33:07.60048+00:00
-- url     : https://prove2.me/theorems/ae3745b4-524b-42fe-b727-d697ac8785f8
-- title:
--   Adapted Poisson counts and null completion under filtration infimum
-- statement:
--   The pointwise infimum retains Poisson-window count measurability and completeness for ambient probability-null sets.
-- source:
--   Kyprianou Chapter 2 exact IsCompletedPoissonFiltration predicate and Mathlib.Filtration complete lattice

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.poissonSInfAdaptedAndNullCompleteV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (S : Set (Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)))
    (hS : ∀ G : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
      G ∈ S → (∀ t u : ℝ≥0, u ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ (G t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A))) ∧
        (∀ t (U : Set Ω), MeasurableSet U → P U = 0 →
      @MeasurableSet Ω (G t) U) ∧ G.IsRightContinuous) :
    (∀ t u : ℝ≥0, u ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ ((sInf S) t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A))) ∧
    (∀ t (U : Set Ω), MeasurableSet U → P U = 0 →
      @MeasurableSet Ω ((sInf S) t) U) := by sorry
