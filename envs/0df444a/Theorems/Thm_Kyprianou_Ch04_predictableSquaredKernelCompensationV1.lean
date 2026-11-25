-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableSquaredKernelCompensationV1
-- name    : Kyprianou.Ch04.predictableSquaredKernelCompensationV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T14:52:48.525796+00:00
-- url     : https://prove2.me/theorems/8a3840dc-29bc-5c3b-ac6f-19f57f8ec9cc
-- title:
--   Compensation identity for squared predictable kernels
-- statement:
--   Apply compensation to the squared admissible kernel.
-- source:
--   Kyprianou (2006), Exercise 4.4.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.predictableSquaredKernelCompensationV1
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
    (t : NNReal) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      ENNReal.ofReal ((phi z.1 z.2 w)^2) ∂(N.N w) ∂P) =
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal ((phi s x w)^2) ∂levyMeasure ∂volume ∂P) := by
  sorry
