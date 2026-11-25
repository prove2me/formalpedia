-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_dominated_event_zero
-- name    : Kyprianou.Ch04.kw47_dominated_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T11:40:10.067592+00:00
-- url     : https://prove2.me/theorems/d549e21e-dcf3-5555-bc38-63d11392c54a
-- title:
--   Dominated limit preserves centred event integrals
-- statement:
--   Apply dominated convergence under the restricted measure of the conditioning event. The approximating integrals are identically zero.
-- source:
--   Kyprianou (2006), Exercise 4.7; deterministic product-grid martingale transfer.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_dominated_event_zero
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (A : Set Omega) (Q : Nat → Omega → Real) (R B : Omega → Real)
    (hQ : ∀ n, Integrable (Q n) P) (hB : Integrable B P)
    (hBound : ∀ n, ∀ᵐ w ∂P, ‖Q n w‖ ≤ B w)
    (hLim : ∀ᵐ w ∂P, Tendsto (fun n => Q n w) atTop (nhds (R w)))
    (hZero : ∀ n, (∫ w in A, Q n w ∂P) = 0) :
    (∫ w in A, R w ∂P) = 0 := by sorry
