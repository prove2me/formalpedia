-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalAbsoluteLedgerMeasurableV1
-- name    : Kyprianou.Ch04.physicalAbsoluteLedgerMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:09:08.142508+00:00
-- url     : https://prove2.me/theorems/5269a347-6f97-5279-9e60-875aabe2ed47
-- title:
--   physicalAbsoluteLedgerMeasurableV1
-- statement:
--   physicalAbsoluteLedgerMeasurableV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), uniform cutoff probability envelope

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The absolute physical mark integral is a measurable nonnegative random variable,
with no moment requirement on the mark law. -/

theorem Kyprianou.Ch04.physicalAbsoluteLedgerMeasurableV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    Measurable (fun w => ∫ z in D, |z.2| ∂(N.N w)) := by
  sorry
