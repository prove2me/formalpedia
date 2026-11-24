-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compensatedJumpIntegralTrueMartingaleAdaptedV2
-- name    : Kyprianou.Ch04.compensatedJumpIntegralTrueMartingaleAdaptedV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:12:50.945218+00:00
-- url     : https://prove2.me/theorems/de803659-8b04-445d-8bb1-ab4d0aebbe73
-- title:
--   Corollary 4.6: compensated jump integral true martingale (common null event and adapted PRM correction)
-- statement:
--   Use a common almost-sure continuity event for all marks, measurable past random-measure evaluations, and joint past-horizon measurability of the marked integrand. These are the structural measurability requirements for the exact adapted martingale process, in addition to the original finite expected compensator.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.6, printed page 97.; correction of the formalisation of 61a5bc8c-34e9-49c2-b76f-9c0e0650fed4.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compensatedJumpIntegralTrueMartingaleAdaptedV2
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))
    (hPast : ∀ (t : NNReal) (B : Set (Real × Real)),
      MeasurableSet B →
      B ⊆ Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ →
      Measurable[F t] (fun omega => N.N omega B))
    (hKernelPast : ∀ t : NNReal,
      Measurable[(F t).prod inferInstance]
        (fun z : Omega × (Real × Real) =>
          if z.2.1 ∈ Set.Icc (0 : Real) (t : Real)
          then phi z.2.1 z.2.2 z.1 else 0))
    (hFinite : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤) :
    MeasureTheory.Martingale
      (fun (t : NNReal) omega =>
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          phi z.1 z.2 omega ∂(N.N omega)) -
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x, phi s x omega ∂levyMeasure) ∂volume))
      F P := by
  sorry
end Kyprianou.Ch04
