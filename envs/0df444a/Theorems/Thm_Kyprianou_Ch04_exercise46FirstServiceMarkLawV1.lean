-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstServiceMarkLawV1
-- name    : Kyprianou.Ch04.exercise46FirstServiceMarkLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:34:45.934801+00:00
-- url     : https://prove2.me/theorems/d76254ad-c1b0-4576-9e00-7c19d6ec3619
-- title:
--   First physical service mark has the service law
-- statement:
--   For an attained almost surely finite first physical negative jump, the positive jump magnitude is measurable and has the service distribution.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstServiceMarkLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hFirst : ∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
      0 < (A w).untopD 0 ∧
      L.X ((A w).untopD 0) w <
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
      ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x)) :
    let J : Omega → Real := fun w =>
      -(L.X ((A w).untopD 0) w -
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0))
    Measurable J ∧ P.map J = service := by
  sorry
