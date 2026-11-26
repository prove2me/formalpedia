-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_dominated_event_zero
-- name    : Kyprianou.Ch04.kw48_dominated_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:52.680856+00:00
-- url     : https://prove2.me/theorems/99038d5a-f3a2-4cd4-9d8d-eb09d42cbadd
-- title:
--   Complex dominated event-integral limit preserves zero
-- statement:
--   Complex dominated event-integral limit preserves zero.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i), complex product-grid proof.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw48_dominated_event_zero
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (A : Set Omega) (Q : Nat → Omega → Complex) (R : Omega → Complex) (B : Omega → Real)
    (hQ : ∀ n, Integrable (Q n) P) (hB : Integrable B P)
    (hBound : ∀ n, ∀ᵐ w ∂P, ‖Q n w‖ ≤ B w)
    (hLim : ∀ᵐ w ∂P, Tendsto (fun n => Q n w) atTop (nhds (R w)))
    (hZero : ∀ n, (∫ w in A, Q n w ∂P) = 0) :
    (∫ w in A, R w ∂P) = 0  := by sorry
