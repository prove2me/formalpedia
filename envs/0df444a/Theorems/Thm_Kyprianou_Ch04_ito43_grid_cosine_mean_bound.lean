-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_cosine_mean_bound
-- name    : Kyprianou.Ch04.ito43_grid_cosine_mean_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:11:49.255152+00:00
-- url     : https://prove2.me/theorems/f70d720a-3622-4816-80bf-d77376b8ad6f
-- title:
--   Expected total cosine deficit bounded uniformly on fine grids
-- statement:
--   Expected total cosine deficit bounded uniformly on fine grids.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform first moment of the total cosine deficit on a fine deterministic grid. -/

theorem Kyprianou.Ch04.ito43_grid_cosine_mean_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (T : NNReal) (ξ : ℝ) (n : ℕ) (hn : 0 < n)
    (hh : (T : ℝ)/(n : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ ≤ 1) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let F : Ω → ℝ := fun w => ∑ k ∈ Finset.range n,
      (1 - Real.cos (ξ * (X (u (k+1)) w - X (u k) w)))
    Integrable F P ∧ (∀ w, 0 ≤ F w) ∧
      (∫ w, F w ∂P) ≤ 2 * (T : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ := by sorry
