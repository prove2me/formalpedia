-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_localised_bound
-- name    : Kyprianou.Ch04.ito43_grid_energy_localised_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:50:41.634869+00:00
-- url     : https://prove2.me/theorems/d49a57dd-a260-4411-9c5e-22a77bf419c0
-- title:
--   Localised stopped grid energy bounded by cosine deficits
-- statement:
--   On a bounded path, the stopped quadratic energy is bounded by a constant times full-grid cosine deficits plus one oscillation square.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- On a bounded path, the stopped grid energy is controlled by full-grid cosine deficits. -/

theorem Kyprianou.Ch04.ito43_grid_energy_localised_bound (X : NNReal → ℝ) (T R t : NNReal) (hR : 0 < R) (ht : t ≤ T)
    (n : ℕ) (hn : 0 < n)
    (hX : ∀ a b : NNReal, a ≤ T → b ≤ T → |X a - X b| ≤ (R : ℝ)) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n, (X (v (k+1)) - X (v k))^2) ≤
      (Real.pi^2 * (R : ℝ)^2 / 2) *
        (∑ k ∈ Finset.range n, (1-Real.cos ((X (u (k+1)) - X (u k))/(R : ℝ)))) +
          (R : ℝ)^2 := by sorry
