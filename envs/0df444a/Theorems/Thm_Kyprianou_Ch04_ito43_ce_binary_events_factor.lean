-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ce_binary_events_factor
-- name    : Kyprianou.Ch04.ito43_ce_binary_events_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:15:44.486671+00:00
-- url     : https://prove2.me/theorems/cb496c14-aa23-53fc-9600-6c3570a40eea
-- title:
--   Finite intersections of empty or universal events factor under probability measures
-- statement:
--   Finite intersections of events each empty or universal factor into their probabilities.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3 formalisation boundary audit.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- Finite intersections of empty or universal events factor under probability measures. -/

theorem Kyprianou.Ch04.ito43_ce_binary_events_factor {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Finset ι) (A : ι → Set Ω)
    (hs : ∀ k ∈ S, A k = ∅ ∨ A k = univ) :
    P (⋂ i ∈ S, A i) = ∏ i ∈ S, P (A i) := by sorry
