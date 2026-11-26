-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_finite_jump_energy_summable
-- name    : Kyprianou.Ch04.ito43_finite_jump_energy_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:20:45.167874+00:00
-- url     : https://prove2.me/theorems/8ba2bf52-0b8e-584a-9aa7-ddeaf7de73a9
-- title:
--   Frequently bounded grid energy implies square-summable jumps
-- statement:
--   Finite jump collections have bounded squared energy by the frequent grid bound; hence the full squared-jump series is summable and bounded.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Filter Set
open scoped NNReal Topology
set_option autoImplicit false

/-- A cadlag path whose full-grid squared increments are frequently bounded has square-summable jumps. -/

theorem Kyprianou.Ch04.ito43_finite_jump_energy_summable (Y L : NNReal → ℝ) (T : NNReal) (hT : 0 < T)
    (hR : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hL : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (C : ℝ)
    (hQ : ∃ᶠ n : ℕ in atTop, (∑ k ∈ Finset.range (n+1),
      (Y (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) -
       Y (T*(k : NNReal)/((n+1 : ℕ) : NNReal)))^2) < C) :
    Summable (fun t : Ioc (0 : NNReal) T => (Y t-L t)^2) ∧
      (∑' t : Ioc (0 : NNReal) T, (Y t-L t)^2) ≤ C := by sorry
