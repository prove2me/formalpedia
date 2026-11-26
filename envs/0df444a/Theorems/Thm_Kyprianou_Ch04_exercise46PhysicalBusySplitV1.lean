-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PhysicalBusySplitV1
-- name    : Kyprianou.Ch04.exercise46PhysicalBusySplitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:22:42.093285+00:00
-- url     : https://prove2.me/theorems/d2e73a1d-6b1c-46c9-87a8-8737b3dd1873
-- title:
--   Exact physical busy-start restart at the first recovery
-- statement:
--   The first busy start is A. Up to recovery the running maximum is A; no other busy start can occur by the no-arrival-at-prelevel theorem. At finite recovery the path is at a record and shifted busy starts correspond bijectively.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PhysicalBusySplitV1
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
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => sSup ((fun u => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w)))
    (hNo : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → A w < (t : WithTop NNReal) →
      Function.leftLim (fun u : NNReal => L.X u w) t =
        (((A w).untopD 0 : NNReal) : Real) →
      ¬ L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t)
    (C : (NNReal → Real) → ENNReal)
    (hOriginal : ∀ᵐ w ∂P, C (fun t => L.X t w) =
      (({t : NNReal | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u => L.X u w) '' Iic t) - L.X t w}).encard : ENNReal))
    (hShiftCount : ∀ w s, let Y : NNReal → Real := fun t => L.X (s+t) w - L.X s w
      C Y = (({t : NNReal | 0 < t ∧ sSup (Y '' Iic t) = Function.leftLim Y t ∧
        Y t < Function.leftLim Y t}).encard : ENNReal)) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    ∀ᵐ w ∂P,
      (R w ≠ ⊤ → C (fun t => L.X t w) = 1 +
        C (fun u => L.X ((R w).untopD 0 + u) w - L.X ((R w).untopD 0) w)) ∧
      (R w = ⊤ → C (fun t => L.X t w) = 1) := by
  sorry
