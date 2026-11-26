-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CompoundPoissonTailLimitV1
-- name    : Kyprianou.Ch05.exercise52CompoundPoissonTailLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:27.038303+00:00
-- url     : https://prove2.me/theorems/e43c2fe1-becb-5e01-80f5-e9e38cc5a10d
-- title:
--   Unkilled compound Poisson comparison joint passage tail converges for a positive nonlattice finite-mean jump law
-- statement:
--   Unkilled compound Poisson comparison joint passage tail converges for a positive nonlattice finite-mean jump law
-- source:
--   Kyprianou (2006), Exercise 5.2(ii)

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05

theorem Kyprianou.Ch05.exercise52CompoundPoissonTailLimitV1
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hPos : F (Iic 0) = 0) (hNL : NonLatticeMeasure F)
    (hInt : Integrable (fun z : ℝ => z) F)
    (hX : IsKilledSubordinator P X deathX 0)
    (hCP : ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * X t omega) ∂P) =
        Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F)))
    (hLeft : IsLeftLimitVersion P X Xleft) :
    ∀ u y : ℝ, 0 < u → 0 < y →
      Tendsto (fun x : ℝ => (P {omega : Omega |
        PassageFinite X deathX x omega ∧
        passageOvershoot X deathX x omega ∈ Ioi u ∧
        passageUndershoot X Xleft deathX x omega ∈ Ioi y}).toReal)
        atTop (nhds ((∫ z in Ioi (u+y), (F (Ioi z)).toReal ∂volume) /
          (∫ z : ℝ, z ∂F))) := by
  sorry
