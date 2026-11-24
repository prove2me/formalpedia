-- Prove2me | Theorems.Thm_Kyprianou_Ch03_extendedStoppingDensityExhaustionV1
-- name    : Kyprianou.Ch03.extendedStoppingDensityExhaustionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:09:53.571006+00:00
-- url     : https://prove2.me/theorems/34a9145a-7729-4163-b75a-8967f531ded6
-- title:
--   Exhaustion of finite stopping-time density identities
-- statement:
--   For a nonnegative density with a.e. measurable finite-cut restrictions and exact cut identities, increasing integer cuts exhaust the finite-time event; monotone convergence and Q finiteness give the real integral identity.
-- source:
--   Kyprianou (2006), Corollary 3.11; finite-horizon restriction and monotone exhaustion

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.extendedStoppingDensityExhaustionV1
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (tau : Omega → WithTop NNReal) (A : Set Omega) (g : Omega → Real)
    (hg : ∀ omega, 0 ≤ g omega)
    (hA : ∀ n : Nat, MeasurableSet
      (A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}))
    (hcut : ∀ n : Nat,
      let B := A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}
      AEMeasurable (Set.indicator B g) P ∧
        Q B = ∫⁻ omega, ENNReal.ofReal (Set.indicator B g omega) ∂P) :
    Q (A ∩ {omega : Omega | tau omega ≠ ⊤}) =
      ENNReal.ofReal (∫ omega,
        Set.indicator (A ∩ {eta : Omega | tau eta ≠ ⊤}) g omega ∂P) := by sorry
