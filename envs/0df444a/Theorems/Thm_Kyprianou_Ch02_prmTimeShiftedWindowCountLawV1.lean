-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmTimeShiftedWindowCountLawV1
-- name    : Kyprianou.Ch02.prmTimeShiftedWindowCountLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:40:17.175801+00:00
-- url     : https://prove2.me/theorems/b570e397-a22c-4a03-9b45-9fcbef2197a3
-- title:
--   Time-shift invariance of finite-intensity Poisson marked-window counts
-- statement:
--   For arbitrary finite-intensity measurable mark cell C, the KLS Poisson random measure count on the time-shifted interval (s,s+t]×C has the same law as the count on (0,t]×C. Direct use of PRM.poisson_law and the homogeneous product reference intensity, including a source-faithful right translation of real Lebesgue volume. This count-level result is a key concrete input to the marked finite-simple stationary marginal law and compound-Poisson exponent argument.
-- source:
--   Kyprianou (2006) Chapter 2, homogeneous marked PRM intensity and finite-region Lévy process; LevyStochCalc/Poisson/FiniteActivity.lean and ChaosStep.lean.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmTimeShiftedWindowCountLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (C : Set ℝ) (hC : MeasurableSet C) (hfinite : ν C < ⊤) :
    ∀ s t : ℝ≥0,
      P.map (fun (ω : Ω) =>
        N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ C)) =
      P.map (fun (ω : Ω) =>
        N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C)) := by sorry
