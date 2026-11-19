-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkload_transientHighTraffic
-- name    : Kyprianou.Ch04.stationaryWorkload_transientHighTraffic
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T13:03:08.792164+00:00
-- url     : https://prove2.me/theorems/9423d3e4-3062-4788-b622-6047ee14876e
-- title:
--   stationaryWorkloadGeometricConvolutionV2: Strictly supercritical traffic: almost-sure divergence
-- statement:
--   Strictly supercritical traffic: almost-sure divergence. An exact standalone source conjunct from the complete corrected Chapter 4 theorem, retaining all original binders and assumptions.
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
theorem stationaryWorkload_transientHighTraffic
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
    (1 < rho →
      ∀ w : Real, 0 ≤ w →
        let supX : NNReal → Omega → Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal → Omega → Real := fun t omega =>
          max w (supX t omega) - L.X t omega
        ∀ᵐ omega : Omega ∂P,
          Tendsto (fun t : NNReal => W t omega) atTop atTop) := by
  sorry
end Kyprianou.Ch04
