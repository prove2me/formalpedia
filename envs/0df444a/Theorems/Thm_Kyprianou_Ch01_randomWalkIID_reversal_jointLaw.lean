-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomWalkIID_reversal_jointLaw
-- name    : Kyprianou.Ch01.randomWalkIID_reversal_jointLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:15:01.648979+00:00
-- url     : https://prove2.me/theorems/f33a5a0d-d040-4eb1-aa0b-a36eca99a2cf
-- title:
--   Finite i.i.d. increment vectors have the same distribution after reversal
-- statement:
--   Restricting an independent identically distributed infinite real increment sequence to any finite set of indices gives the product law of its common marginal. The reversed finite vector therefore has exactly the same pushforward distribution as the original finite vector.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(i); iid-increment reversal underlying the ladder path identity

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.randomWalkIID_reversal_jointLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hindep : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hLaw : ∀ i : ℕ, HasLaw (increment i) jumpLaw P)
    (n : ℕ) :
    P.map (fun ω => fun i : Fin n => increment i ω) =
      P.map (fun ω => fun i : Fin n => increment (Fin.rev i) ω) := by sorry
