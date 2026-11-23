-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStartZeroV1
-- name    : Kyprianou.Ch02.prmFiniteRegionStartZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:55:55.979509+00:00
-- url     : https://prove2.me/theorems/ba93c64d-2636-4f27-8648-356eb5a1d769
-- title:
--   Finite-region Poisson integral starts at zero, pathwise
-- statement:
--   The integral over (0,0] × B vanishes for every sample, giving the exact initial-value field of IsLevyProcess.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.8, finite-region Poisson integral; sound decomposition of the Chapter 2 theorem Kyprianou.finiteRegionPoissonIntegralCh02V3 (38df877c-0872-40d5-8b33-bbad3487ba47), itself already linked to Kyprianou.largeJumpProcessLevy (5c06d985-05f1-4c04-aa68-fc6de328bbfa).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionStartZeroV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) :
    (fun (t : ℝ≥0) (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))
      (0 : ℝ≥0) = (fun _ => (0 : ℝ)) := by sorry
