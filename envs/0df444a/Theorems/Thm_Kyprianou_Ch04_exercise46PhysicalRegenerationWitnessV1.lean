-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PhysicalRegenerationWitnessV1
-- name    : Kyprianou.Ch04.exercise46PhysicalRegenerationWitnessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:09:55.021699+00:00
-- url     : https://prove2.me/theorems/4489998e-c91a-4ceb-ac2b-b72099be2379
-- title:
--   Physical first-busy-period recovery and path-count regeneration witnesses
-- statement:
--   Construct the first busy-period recovery stopping time and a common measurable path count. Its finite probability is the service-law Laplace transform. Almost surely the original count agrees with the physical busy-start count; on finite recovery it is one plus the shifted path count, and otherwise it is exactly one. These are the physical regenerative witnesses, rather than an assumed recurrence.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PhysicalRegenerationWitnessV1
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
    let S : Omega → Set NNReal := fun w => {t | 0 < t ∧ Wleft t w = 0 ∧
      0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
    let Y : Omega → (NNReal → Real) := fun w u => L.X u w
    ∃ R : Omega → WithTop NNReal, IsStoppingTime G.rightCont R ∧
      ∃ C : (NNReal → Real) → ENNReal, Measurable C ∧
        (P {w | R w ≠ ⊤}).toReal = ∫ y : Real, Real.exp (-phi * y) ∂service ∧
        (∀ᵐ w ∂P, C (Y w) = ((S w).encard : ENNReal)) ∧
        (∀ᵐ w ∂P,
          (R w ≠ ⊤ → C (Y w) = 1 +
            C (fun u => L.X ((R w).untopD 0 + u) w - L.X ((R w).untopD 0) w)) ∧
          (R w = ⊤ → C (Y w) = 1)) := by
  sorry
