-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45EventuallyAbsentEventsV5
-- name    : Kyprianou.Ch04.exercise45EventuallyAbsentEventsV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:19:58.405286+00:00
-- url     : https://prove2.me/theorems/48328c5d-d618-5de5-97b8-e728ec99c7a2
-- title:
--   Outer probability dominated by eventually absent measurable events
-- statement:
--   Outer probability dominated by eventually absent measurable events
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii), uniform probability transfer

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45EventuallyAbsentEventsV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A E : ℕ → Set Ω) (hm : ∀ n, MeasurableSet (A n))
    (hlim : ∀ᵐ w ∂P, ∀ᶠ n in atTop, w ∉ A n)
    (hb : ∀ n, ∀ᵐ w ∂P, w ∈ E n → w ∈ A n) :
    Tendsto (fun n => (P (E n)).toReal) atTop (nhds 0) := by
  sorry
