-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PhysicalRecoveryClockProbabilityV1
-- name    : Kyprianou.Ch04.exercise46PhysicalRecoveryClockProbabilityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:22:36.681115+00:00
-- url     : https://prove2.me/theorems/58a79545-50ab-532e-88ad-1dcccf4af9d1
-- title:
--   Absolute first recovery clock and probability from first-arrival product law
-- statement:
--   Use dense sampled stopping times, the first-arrival mark law and shifted product law, and the fixed-root strict passage probability.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PhysicalRecoveryClockProbabilityV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hFirst : ∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
      0 < (A w).untopD 0 ∧
      L.X ((A w).untopD 0) w <
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
      ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (hPrefix : ∀ᵐ w ∂P,
      (∀ s : NNReal, s < (A w).untopD 0 → L.X s w = (s : Real)) ∧
      (∀ s : NNReal, L.X s w ≤ (s : Real)))
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x))
    (phi : Real) (hphi : 0 < phi) (hroot : L.ψ phi = 0)
    (hmax : ∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    IsStoppingTime G.rightCont R ∧
      (P {w | R w ≠ ⊤}).toReal = ∫ y : Real, Real.exp (-phi * y) ∂service := by
  sorry
