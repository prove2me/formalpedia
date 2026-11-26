-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricConvolutionV2
-- name    : Kyprianou.Ch04.stationaryWorkloadGeometricConvolutionV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:17:42.626098+00:00
-- url     : https://prove2.me/theorems/460c52ce-8fa4-443f-bc72-17c3809c27f3
-- title:
--   Theorem 4.10: stable workload law, critical regime and geometric convolutions (corrected v2)
-- statement:
--   For spectrally negative bounded-variation input with d>0 and traffic intensity rho, the zero-traffic pure-drift case converges weakly to a Dirac mass at zero. For 0<rho<1, every initial workload converges weakly to the geometric convolution law with atom 1-rho at zero and jump-tail mixing distribution eta. For rho>=1 no invariant probability law exists on nonnegative workloads. For the strictly overloaded rho>1 case workload diverges almost surely. The critical rho=1 case intentionally makes no almost-sure divergence claim.
-- source:
--   Kyprianou (2006), first edition, Theorem 4.10, printed pages 100-102.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.10 (p. 100): weak workload limit, atom, geometric convolution and transient regime. -/
theorem stationaryWorkloadGeometricConvolutionV2
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
              (nhds (∫ x : Real, f x ∂mu)))) ∧
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
            atTop (nhds (f 0))) ∧
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
          ∫ w, f w ∂mu)) ∧
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
