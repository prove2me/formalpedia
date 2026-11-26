-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_remainder_scalar
-- name    : Kyprianou.Ch04.ito43_cosine_remainder_scalar
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:27.908647+00:00
-- url     : https://prove2.me/theorems/647c4dc9-d6e0-51bf-9067-e8a848263842
-- title:
--   Cosine quadratic remainder is globally quadratic and locally smaller
-- statement:
--   Use the lower quadratic bound for cosine for the global estimate. Apply the proved Taylor modulus at zero to the cosine, with second derivative negative cosine, and the Lipschitz bound for cosine to get a cubic error estimate.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_remainder_scalar (a : ℝ) (ha : 0 < a) :
    let r : ℝ → ℝ := fun z => z^2/2-(1-Real.cos (a*z))/a^2
    Continuous r ∧ (∀ z, |r z| ≤ z^2/2) ∧
      ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ z, |z| ≤ δ → |r z| ≤ e*z^2 := by sorry
