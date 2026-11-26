-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkload_nonStationaryCriticalAndAbove
-- name    : Kyprianou.Ch04.stationaryWorkload_nonStationaryCriticalAndAbove
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:03:12.155262+00:00
-- url     : https://prove2.me/theorems/47710614-7b31-4ac0-9719-007edb110b62
-- title:
--   stationaryWorkloadGeometricConvolutionV2: Critical and supercritical traffic: nonexistence of a stationary probability law
-- statement:
--   Critical and supercritical traffic: nonexistence of a stationary probability law. An exact standalone source conjunct from the complete corrected Chapter 4 theorem, retaining all original binders and assumptions.
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
theorem stationaryWorkload_nonStationaryCriticalAndAbove
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
    (1 ≤ rho →
      ¬ ∃ mu : Measure Real,
        IsProbabilityMeasure mu ∧
        mu (Set.Ici (0 : Real)) = 1 ∧
        (∀ (t : NNReal) (f : BoundedContinuousFunction Real Real),
          (∫ w in Set.Ici (0 : Real),
            (∫ omega,
              f (max w
                (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) -
                L.X t omega) ∂P) ∂mu) =
          ∫ w, f w ∂mu)) := by
  sorry
end Kyprianou.Ch04
