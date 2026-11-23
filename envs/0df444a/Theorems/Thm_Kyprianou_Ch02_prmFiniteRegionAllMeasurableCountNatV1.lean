-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionAllMeasurableCountNatV1
-- name    : Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:42:54.283184+00:00
-- url     : https://prove2.me/theorems/f3bf130d-e048-43a4-a7ad-dc911845c899
-- title:
--   Single conull event: every measurable subset of a finite-intensity Poisson window has a natural-number count
-- statement:
--   For an arbitrary LevyStochCalc Poisson random measure N and any finite reference-intensity measurable region R, there is one conull event such that each measurable subset A of the time-mark product space carries a finite natural mass Nω(A∩R). This is a genuinely simultaneous result, strengthening N.integer_valued which only gives a conull event for each individual measurable A. Use a countable π-system generated from the Borel product space and monotone-class/Dynkin closure, as in the actual proved upstream LevyStochCalc.Poisson.ae_isIntegerValued_restrict source.
-- source:
--   Kyprianou (2006) Ch2 finite-activity PRM, LevyStochCalc/Poisson/Atomic.lean theorem ae_isIntegerValued_restrict, direct dependency of Eq. (2.3) via finiteRegionPRMIntegerValuedAllNaturalWindowsV1.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ A : Set (ℝ × ℝ),
      MeasurableSet A → ∃ n : ℕ, N.N ω (A ∩ R) = n := by sorry
