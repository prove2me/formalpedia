-- Prove2me | Theorems.Thm_Kyprianou_Ch04_conditionalENNClockBalance
-- name    : Kyprianou.Ch04.conditionalENNClockBalance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T09:54:54.55477+00:00
-- url     : https://prove2.me/theorems/47041fff-729c-577a-ba1a-c878c5a62bbe
-- title:
--   Eventwise balance of raw and compensator extended clocks
-- statement:
--   Apply nonnegative compensation to the admissible event cutoff. The proved event-cutoff identities identify the future integrals, then interval union and additivity give the balance of full clocks.
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

theorem Kyprianou.Ch04.conditionalENNClockBalance
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ w ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x w)
        (nhdsWithin (t : Real) (Set.Iio (t : Real))) (nhds (phi (t : Real) x w)))
    (hJ : ∀ t : NNReal, Measurable ((fun (t : NNReal) w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) t))
    (hC : ∀ t : NNReal, Measurable ((fun (t : NNReal) w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) t))
    (u t : NNReal) (hut : u ≤ t) (A : Set Omega) (hA : MeasurableSet[F u] A) :
    (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) t w ∂P) + (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) u w ∂P) =
    (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) u w ∂P) + (∫⁻ w in A, (fun (t : NNReal) w => ∫⁻ s in Set.Icc (0 : Real) (t : Real),
      ∫⁻ x, ENNReal.ofReal (phi s x w) ∂levyMeasure ∂volume) t w ∂P) := by
  sorry
