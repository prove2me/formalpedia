-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyStartCountV1
-- name    : Kyprianou.Ch04.exercise46BusyStartCountV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T11:39:19.235863+00:00
-- url     : https://prove2.me/theorems/881f8276-a75b-51cf-aa54-39bf83aca5f2
-- title:
--   Exercise 4.6(ii): finite geometric count of actual busy starts
-- statement:
--   For the unit-drift overloaded compound Poisson storage process with positive service law, the actual starts identified by zero left workload and strictly positive post-jump workload are almost surely finite. Their count has the geometric law with success probability one minus the service Laplace transform at the positive maximal zero root.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii), regenerative busy period law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyStartCountV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation)
    (hDrift : L.drift = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Set.Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν =
      ENNReal.ofReal lambda •
        (service.map (fun x : Real => -x)))
    (Wleft : NNReal -> Omega -> Real)
    (hWLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal =>
          sSup ((fun u : NNReal => L.X u omega) '' Set.Iic s) -
          L.X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Wleft t omega)))
    (rho : Real)
    (hRho : rho =
      lambda * (∫ y : Real, y ∂service))
    (hSupercritical : 1 < rho)
    (phi : Real) (hphi : 0 < phi) (hroot : L.ψ phi = 0)
    (hmax : ∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Iic t)
    let W : NNReal → Omega → Real := fun t omega => supX t omega - L.X t omega
    let busyStarts : Omega → Set NNReal := fun omega =>
      {t : NNReal | 0 < t ∧ Wleft t omega = 0 ∧ 0 < W t omega}
    let p : Real := 1 - ∫ y : Real, Real.exp (-phi * y) ∂service
    (∀ᵐ omega : Omega ∂P, (busyStarts omega).Finite) ∧
      ∀ k : Nat, (P {omega : Omega | (busyStarts omega).ncard = k + 1}).toReal =
        p * (1 - p) ^ k := by
  sorry
