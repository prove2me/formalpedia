-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricConvolution
-- name    : Kyprianou.Ch04.stationaryWorkloadGeometricConvolution
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:26:06.979013+00:00
-- url     : https://prove2.me/theorems/e44fcbd1-01b4-4409-ad47-947d7c048728
-- title:
--   Theorem 4.10: stationary workload law and geometric convolutions
-- statement:
--   For spectrally negative bounded-variation Levy input d>0 with rho=(1/d) integral jump size nu, when 0<rho<1, all initial workloads converge weakly in law to the same probability measure mu. Its law has atom 1-rho at zero and exact geometric mixture (1-rho) sum_{n>=0} rho^n eta^{*n}, where eta(dx)=nu(x,infinity)/(d rho) dx; weak convergence is tested against every bounded continuous function. When rho>=1 workload tends to positive infinity almost surely, excluding any nontrivial finite stationary law. The extended rho includes infinite first moments. In the rho>=1 regime there is explicitly no stationary probability law supported on nonnegative workloads: no such law is invariant under the workload transition semigroup, tested against every bounded continuous function.
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
theorem stationaryWorkloadGeometricConvolution
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
    (1 ≤ rho →
      (∀ w : Real, 0 ≤ w →
        let supX : NNReal → Omega → Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal → Omega → Real := fun t omega =>
          max w (supX t omega) - L.X t omega
        ∀ᵐ omega : Omega ∂P,
          Tendsto (fun t : NNReal => W t omega) atTop atTop) ∧
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
