-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_finite_jump_energy_lower
-- name    : Kyprianou.Ch04.ito43_finite_jump_energy_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:19:29.926125+00:00
-- url     : https://prove2.me/theorems/ab38747a-b824-43b3-b1f0-30828ba8c387
-- title:
--   Finite actual jump energy is an eventual lower bound on grid energy
-- statement:
--   Finite actual jump energy is an eventual lower bound on grid energy.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Filter Set
open scoped NNReal Topology
set_option autoImplicit false

/-- Every finite jump energy below the horizon is an eventual lower bound up to any strict slack. -/

theorem Kyprianou.Ch04.ito43_finite_jump_energy_lower (Y L : NNReal → ℝ) (T : NNReal) (hT : 0 < T)
    (hR : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hL : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (S : Finset NNReal) (hS : ∀ t ∈ S, 0 < t ∧ t ≤ T)
    (C : ℝ) (hC : C < ∑ t ∈ S, (Y t-L t)^2) :
    ∀ᶠ n : ℕ in atTop, C ≤ ∑ k ∈ Finset.range (n+1),
      (Y (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) -
       Y (T*(k : NNReal)/((n+1 : ℕ) : NNReal)))^2 := by sorry
