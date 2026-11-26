-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyRegenerativeTailV1
-- name    : Kyprianou.Ch04.exercise46BusyRegenerativeTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:56:11.730799+00:00
-- url     : https://prove2.me/theorems/8a182aac-751c-563b-b23e-5a593455310c
-- title:
--   Regenerative recurrence for the physical busy-start tail
-- statement:
--   Show the recurrence by regenerating the input process on finite recovery of the first busy period.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyRegenerativeTailV1
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
    ∀ k : Nat,
      (P {omega | ((k + 1 + 1 : Nat) : ENat) ≤ (busyStarts omega).encard}).toReal =
        (1 - p) * (P {omega | ((k + 1 : Nat) : ENat) ≤
          (busyStarts omega).encard}).toReal := by
  sorry
