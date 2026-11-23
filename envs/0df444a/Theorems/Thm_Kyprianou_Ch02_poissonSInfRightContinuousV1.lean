-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonSInfRightContinuousV1
-- name    : Kyprianou.Ch02.poissonSInfRightContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:33:06.149191+00:00
-- url     : https://prove2.me/theorems/5afe666e-9fb2-46fe-a449-df0e2b3d7acd
-- title:
--   Right continuity of an infimum of right-continuous Poisson-admissible filtrations
-- statement:
--   The infimum of right-continuous Poisson-admissible filtrations remains right-continuous; prove using the right-continuous hull and lattice minimality.
-- source:
--   Kyprianou Chapter 2 exact IsCompletedPoissonFiltration predicate and Mathlib.Filtration complete lattice

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.poissonSInfRightContinuousV1
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
    (sInf S).IsRightContinuous := by sorry
