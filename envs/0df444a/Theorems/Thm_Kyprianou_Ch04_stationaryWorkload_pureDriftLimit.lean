-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkload_pureDriftLimit
-- name    : Kyprianou.Ch04.stationaryWorkload_pureDriftLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:03:13.019277+00:00
-- url     : https://prove2.me/theorems/1a0abeac-9074-4758-87f0-03018bc501fd
-- title:
--   stationaryWorkloadGeometricConvolutionV2: Zero-traffic pure-drift weak limit
-- statement:
--   Zero-traffic pure-drift weak limit. An exact standalone source conjunct from the complete corrected Chapter 4 theorem, retaining all original binders and assumptions.
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
theorem stationaryWorkload_pureDriftLimit
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
    (rho = 0 →
      ∀ w : Real, 0 ≤ w →
        let supX : NNReal → Omega → Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal → Omega → Real := fun t omega =>
          max w (supX t omega) - L.X t omega
        ∀ f : BoundedContinuousFunction Real Real,
          Tendsto
            (fun t : NNReal =>
              ∫ omega, f (W t omega) ∂P)
            atTop (nhds (f 0))) := by
  sorry
end Kyprianou.Ch04
