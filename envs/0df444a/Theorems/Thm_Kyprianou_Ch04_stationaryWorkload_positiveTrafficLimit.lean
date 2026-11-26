-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkload_positiveTrafficLimit
-- name    : Kyprianou.Ch04.stationaryWorkload_positiveTrafficLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:03:07.284339+00:00
-- url     : https://prove2.me/theorems/d54438b2-7002-4723-bcc5-e621c7733ba4
-- title:
--   stationaryWorkloadGeometricConvolutionV2: Positive subcritical traffic: invariant law, atom, geometric mixture and weak convergence
-- statement:
--   Positive subcritical traffic: invariant law, atom, geometric mixture and weak convergence. An exact standalone source conjunct from the complete corrected Chapter 4 theorem, retaining all original binders and assumptions.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Theorem 4.10, printed p. 100

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.10 (p. 100): weak workload limit, atom, geometric convolution and transient regime. -/
theorem stationaryWorkload_positiveTrafficLimit
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
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
    (0 < rho → rho < 1 →
      ∃ mu : Measure Real,
        IsProbabilityMeasure mu ∧
        IsProbabilityMeasure eta ∧
        mu {0} = 1 - rho ∧
        (∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B)) ∧
        (∀ w : Real, 0 ≤ w →
          let supX : NNReal → Omega → Real := fun t omega =>
            sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
          let W : NNReal → Omega → Real := fun t omega =>
            max w (supX t omega) - L.X t omega
          ∀ f : BoundedContinuousFunction Real Real,
            Tendsto
              (fun t : NNReal =>
                ∫ omega, f (W t omega) ∂P)
              atTop
              (nhds (∫ x : Real, f x ∂mu)))) := by
  sorry
end Kyprianou.Ch04
