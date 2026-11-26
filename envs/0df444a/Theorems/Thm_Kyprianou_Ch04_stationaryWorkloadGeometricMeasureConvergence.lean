-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricMeasureConvergence
-- name    : Kyprianou.Ch04.stationaryWorkloadGeometricMeasureConvergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:04:51.95815+00:00
-- url     : https://prove2.me/theorems/99fb7227-b8e9-4ca2-8c56-cb8dd3d3b73e
-- title:
--   Weak convergence to the exact geometric convolution workload law
-- statement:
--   For subcritical positive traffic, the reflected bounded-variation Lévy workload converges weakly to the probability measure with the specified geometric convolution series. The existence, probability normalisation and atom of that measure are proved independently; this obligation is precisely the remaining stochastic convergence statement.
-- source:
--   Kyprianou (2006) Theorem 4.10 p. 100, geometric convolution stationary law, exact source interface.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.stationaryWorkloadGeometricMeasureConvergence
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    let eta : Measure Real :=
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun x : Real =>
          L.ν (Set.Iio (-x)) /
            (ENNReal.ofReal L.drift * rho))
    let convPow : Nat → Measure Real :=
      Nat.rec (Measure.dirac (0 : Real))
        (fun _ mu => mu.conv eta)
    0 < rho → rho < 1 →
      ∀ mu : Measure Real,
        IsProbabilityMeasure mu →
        (∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B)) →
        ∀ w : Real, 0 ≤ w →
          let supX : NNReal → Omega → Real := fun t omega =>
            sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
          let W : NNReal → Omega → Real := fun t omega =>
            max w (supX t omega) - L.X t omega
          ∀ f : BoundedContinuousFunction Real Real,
            Tendsto
              (fun t : NNReal =>
                ∫ omega, f (W t omega) ∂P)
              atTop
              (nhds (∫ x : Real, f x ∂mu)) := by
  sorry
