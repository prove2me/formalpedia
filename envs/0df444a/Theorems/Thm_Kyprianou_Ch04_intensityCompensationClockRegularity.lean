-- Prove2me | Theorems.Thm_Kyprianou_Ch04_intensityCompensationClockRegularity
-- name    : Kyprianou.Ch04.intensityCompensationClockRegularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T09:55:03.07793+00:00
-- url     : https://prove2.me/theorems/4f7ee049-2976-50d6-9d2a-30db13a30a04
-- title:
--   Intensity clock adaptedness and almost-sure real conversion
-- statement:
--   Use the measurable cutoff kernel under the current filtration to obtain both measurable nested integrals. Finite expected intensity gives almost-sure finite inner extended clock, permitting real conversion.
-- source:
--   Kyprianou (2006), corrected Corollary 4.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.intensityCompensationClockRegularity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (t : NNReal)
    (hKernelPast : Measurable[(F t).prod inferInstance]
      (fun z : Omega × (Real × Real) =>
        if z.2.1 ∈ Set.Icc (0 : Real) (t : Real) then phi z.2.1 z.2.2 z.1 else 0))
    (hFinite : (∫⁻ w, ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume ∂P) < ⊤) :
    Measurable[F t] (fun w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) ∧
    StronglyMeasurable[F t] (fun w => ∫ s in Set.Icc (0 : Real) (t : Real),
      ∫ x, phi s x w ∂levyMeasure ∂volume) ∧
    (fun w => ∫ s in Set.Icc (0 : Real) (t : Real),
      ∫ x, phi s x w ∂levyMeasure ∂volume) =ᵐ[P]
    (fun w => (∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume).toReal) := by
  sorry
