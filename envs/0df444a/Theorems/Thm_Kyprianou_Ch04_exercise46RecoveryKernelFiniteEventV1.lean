-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryKernelFiniteEventV1
-- name    : Kyprianou.Ch04.exercise46RecoveryKernelFiniteEventV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:26:15.409849+00:00
-- url     : https://prove2.me/theorems/08098b83-bf47-582e-a372-1200ba89e4fb
-- title:
--   Absolute and shifted recovery clocks have the same finite event
-- statement:
--   A crossing above the arrival height is equivalent to crossing above the service mark in shifted coordinates. Use the linear prefix to identify the left arrival value.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RecoveryKernelFiniteEventV1
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
    (K : Real × (NNReal → Real) → WithTop NNReal)
    (hKshift : ∀ (w : Omega) (s : NNReal) (x : Real),
      K (x,fun u => L.X (s+u) w - L.X s w) =
        ⨅ u : NNReal, if x < L.X (s+u) w - L.X s w
          then (u : WithTop NNReal) else ⊤) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    let a : Omega → NNReal := fun w => (A w).untopD 0
    let J : Omega → Real := fun w => -(L.X (a w) w -
      Function.leftLim (fun u : NNReal => L.X u w) (a w))
    let Z : Omega → (NNReal → Real) := fun w u => L.X (a w+u) w - L.X (a w) w
    ∀ᵐ w ∂P, R w = ⊤ ↔ K (J w,Z w) = ⊤ := by
  sorry
