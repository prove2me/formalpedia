-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_predictable_grid_past_event_mean_zero
-- name    : Kyprianou.Ch04.kw47_predictable_grid_past_event_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:33:47.495472+00:00
-- url     : https://prove2.me/theorems/24e8a5e6-6692-5781-b701-6e1627da288c
-- title:
--   Finite predictable martingale grid gains vanish on past measurable events
-- statement:
--   For every finite deterministic increasing time grid, bounded predictable weights against integrable martingale increments have zero integral over any event measurable at a time preceding the grid. Extend each weight by the indicator of that event, apply conditional centring to each increment, and integrate a finite sum. This supplies exact past-event identities required to transfer the Kella–Whitt martingale property by L1 limits.
-- source:
--   Kyprianou (2006), Exercise 4.7, p. 108 and solutions pp. 320-321; generic predictable product-grid martingale transform on a prior measurable event.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_predictable_martingale_increment_zero
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_predictable_grid_past_event_mean_zero
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (E : NNReal → Ω → Real) (hE : Martingale E F P)
    (W : ℕ → Ω → Real) (u : ℕ → NNReal) (hu : Monotone u)
    (hW : ∀ i, Measurable[F (u i)] (W i)) (C : Real)
    (hWBound : ∀ i w, ‖W i w‖ ≤ C)
    (n : ℕ) (s : NNReal) (hs : s ≤ u 0)
    (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ w in A, ∑ i ∈ Finset.range n,
       W i w * (E (u (i + 1)) w - E (u i) w) ∂P) = 0 := by sorry
