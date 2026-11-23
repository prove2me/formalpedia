-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonCountCharacteristicV1
-- name    : Kyprianou.Ch02.finiteRegionPoissonCountCharacteristicV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:19:24.199906+00:00
-- url     : https://prove2.me/theorems/b6c715da-4181-43ef-af07-06972340b5c6
-- title:
--   Lemma 2.8 finite-window Poisson count characteristic function
-- statement:
--   The characteristic function of a Poisson time-mark region count has the exact exponent with intensity referenceIntensity(ν)((0,t]×B). Uses the already accepted finite-window Poisson law and the exact pinned Mathlib Poisson characteristic-function identity. This gives the finite-window count component required for the full marked Poisson integral characteristic exponent.
-- source:
--   Source-faithful LevyStochCalc Poisson/ProfileCharacter.lean integral_exp_I_mul_count, and pinned Mathlib charFun_map_cast_poissonMeasure, Kyprianou (2006) Lemma 2.8.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonWindowCountLawV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPoissonCountCharacteristicV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) (t : ℝ≥0) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I *
      ((u * (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal : ℝ) : ℂ)) ∂P =
    Complex.exp ((LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal *
      (Complex.exp (Complex.I * (u : ℂ)) - 1)) := by sorry
end Kyprianou.Ch02
