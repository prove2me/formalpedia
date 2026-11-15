-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1StationaryWorkload
-- name    : Kyprianou.Ch04.exercise46MM1StationaryWorkload
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:28:16.111898+00:00
-- url     : https://prove2.me/theorems/09740689-7fee-4692-aac9-f25ad1d26310
-- title:
--   Exercise 4.6(iii): M/M/1 limiting workload atom and exponential component
-- statement:
--   For compound-Poisson downward exponential service jumps of rate lambda and parameter mu, upward service rate d=1, and 0<lambda<mu, prove that the workload from initial zero converges weakly to (1-lambda/mu) times the sum of a unit point mass at zero and positive density lambda exp(-(mu-lambda)x) dx. This is the complete M/M/1 specialisation of Theorem 4.10.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Exercise 4.6(iii), pp. 105-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Exercise 4.6(iii) (p. 108). M/M/1 limiting workload mixture. -/
theorem exercise46MM1StationaryWorkload
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (lambda mu : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu)
    (hd : L.drift = 1)
    (hServiceLaw :
      L.ν =
        ((volume : Measure Real).restrict (Set.Iio 0)).withDensity
          (fun y : Real =>
            ENNReal.ofReal (lambda * mu * Real.exp (mu * y)))) :
    ∃ stationary : Measure Real,
      IsProbabilityMeasure stationary ∧
      stationary =
        ENNReal.ofReal (1 - lambda / mu) •
          ((Measure.dirac (0 : Real)) +
            ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
              (fun x : Real =>
                ENNReal.ofReal (lambda * Real.exp (-(mu - lambda) * x)))) ∧
      (∀ f : BoundedContinuousFunction Real Real,
        let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal -> Omega -> Real := fun t omega =>
          supX t omega - L.X t omega
        Tendsto
          (fun t : NNReal => ∫ omega, f (W t omega) ∂P)
          atTop (nhds (∫ x : Real, f x ∂stationary))) := by
  sorry
end Kyprianou.Ch04
