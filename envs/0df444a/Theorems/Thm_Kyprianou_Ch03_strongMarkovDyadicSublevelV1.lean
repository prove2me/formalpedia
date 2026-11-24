-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovDyadicSublevelV1
-- name    : Kyprianou.Ch03.strongMarkovDyadicSublevelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:13:46.941166+00:00
-- url     : https://prove2.me/theorems/cc87304d-951d-4767-9961-5ea555bc627b
-- title:
--   Extended dyadic clock sublevel identity
-- statement:
--   A finite dyadic ceiling index lies below j exactly when the extended stopping clock lies below the corresponding grid time.
-- source:
--   Kyprianou (2006), Theorem 3.1; dyadic fibre measurability 549813ab-58fc-4e59-ab0b-175afdb53dbe.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovDyadicSublevelV1
    {Omega : Type} (tau : Omega → WithTop NNReal)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (n j : ℕ) (w : Omega) :
    (tau w ≠ ⊤ ∧ Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) ≤ j) ↔
      tau w ≤ (((j : NNReal) / (2 : NNReal)^n : NNReal) : WithTop NNReal) := by
  sorry
