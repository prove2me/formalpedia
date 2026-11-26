-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ucp_countable_envelope
-- name    : Kyprianou.Ch04.ito43_ucp_countable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:14:19.576172+00:00
-- url     : https://prove2.me/theorems/f2910579-90cc-58f9-ae70-a802ac5f46e0
-- title:
--   Almost-sure convergence of a measurable error envelope implies uniform-in-probability convergence
-- statement:
--   Almost-sure convergence of a measurable error envelope implies uniform-in-probability convergence.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Almost-sure convergence of a measurable error envelope implies UCP convergence,
even when the error event itself is not known to be measurable. -/

theorem Kyprianou.Ch04.ito43_ucp_countable_envelope {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℕ → NNReal → Ω → ℝ) (B : ℕ → Ω → ℝ) (T : NNReal)
    (hB : ∀ n, AEStronglyMeasurable (B n) P)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => B n w) atTop (nhds 0))
    (hbound : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |E n t w| ≤ |B n w|)
    (e : ℝ) (he : 0 < e) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) := by sorry
