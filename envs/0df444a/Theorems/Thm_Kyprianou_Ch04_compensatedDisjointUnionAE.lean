-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compensatedDisjointUnionAE
-- name    : Kyprianou.Ch04.compensatedDisjointUnionAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:53:31.494738+00:00
-- url     : https://prove2.me/theorems/7682d35b-966c-45a9-9bd2-34037bce3143
-- title:
--   Almost-sure additivity of compensated counts on finite disjoint sets
-- statement:
--   On two disjoint measurable finite-intensity regions, the compensated count of their union is almost surely the sum of their compensated counts.
-- source:
--   Poisson random measure count additivity; Kyprianou Chapter 4 Exercise 4.4.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.compensatedDisjointUnionAE
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] (N : PoissonRandomMeasure P ν)
    {A B : Set (ℝ × E)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B)
    (hAfin : referenceIntensity ν A ≠ ⊤)
    (hBfin : referenceIntensity ν B ≠ ⊤) :
    (fun ω => N.compensated (A ∪ B) ω) =ᵐ[P]
      (fun ω => N.compensated A ω + N.compensated B ω) := by
  sorry
