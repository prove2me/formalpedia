-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralMeasurableKLSV1
-- name    : Kyprianou.Ch02.prmFiniteSimpleMarkIntegralMeasurableKLSV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:17:09.836171+00:00
-- url     : https://prove2.me/theorems/04cde359-66ed-4e06-9b5d-045719cc65e8
-- title:
--   Measurability of a finite-simple signed mark integral against the KLS Poisson random measure
-- statement:
--   For any measurable time-mark region R and real-valued simple mark f, the raw signed Bochner setIntegral wrt KLS PoissonRandomMeasure is measurable as a random variable. Derive from the proved Kyprianou.Ch02.prmNonnegativeIntegralMeasurableLocalEvalSigmaV1 for arbitrary nonnegative measurable integrands and its positive/negative decomposition, or directly via integral of finite simple function against measurable evaluation family. Needed for the Eq (2.3) simple integral law.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleMarkIntegralMeasurableKLSV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (f : SimpleFunc ℝ ℝ) :
    Measurable (fun (ω : Ω) =>
      ∫ z in R, f z.2 ∂(N.N ω)) := by sorry
