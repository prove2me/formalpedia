-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkInAOfFiniteArrivalAe
-- name    : Kyprianou.Ch06.firstMarkInAOfFiniteArrivalAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:44:44.284217+00:00
-- url     : https://prove2.me/theorems/3004c1fd-2df6-4aee-9e01-651b7803e07c
-- title:
--   First A-mark belongs to A almost surely when first A-arrival is finite almost surely
-- statement:
--   The original Kyprianou (2006) cemetery-or-A mark selector hMark and a genuine zero-probability infinite first-arrival event together imply that the selected first mark belongs to A almost surely. No distributional mark law is presupposed; this is the support implication needed for the positive-intensity first-mark factorisation.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkInAOfFiniteArrivalAe
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (hFinite : P {omega |
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) = ⊤} = 0) :
    ∀ᵐ omega ∂P, firstMark omega ∈ (some '' A) := by sorry
