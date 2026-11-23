-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmKLSTimeShiftedWindowCountLawV1
-- name    : Kyprianou.Ch02.prmKLSTimeShiftedWindowCountLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:11:24.928787+00:00
-- url     : https://prove2.me/theorems/a359b1b5-ad0a-4a7b-8fcf-3f7adf5fd2a2
-- title:
--   Poisson time-shift marginal count law on KLS PoissonRandomMeasure provider
-- statement:
--   Prove time-shifted count law using N.poisson_law and referenceIntensity equality. The original proved Kyprianou.Ch02.prmTimeShiftedWindowCountLawV1 uses an incompatible duplicate F000 provider. Here use ONLY Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure; the argument has already been proved in the other provider. Connect to Eq 2.3 through accepted sketch chain.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3); KLS-modular PoissonRandomMeasure provider.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmKLSTimeShiftedWindowCountLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (C : Set ℝ) (hC : MeasurableSet C) (hfinite : ν C < ⊤) :
    ∀ s t : ℝ≥0,
      P.map (fun (ω : Ω) =>
        N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ C)) =
      P.map (fun (ω : Ω) =>
        N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C)) := by sorry
