-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_density_measurable_mono
-- name    : Kyprianou.Ch08.StageB.p2m89_density_measurable_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:24:40.890604+00:00
-- url     : https://prove2.me/theorems/02702730-0186-47a1-a44b-f9a1f2198175
-- title:
--   Translated densities are measurable and increasing
-- statement:
--   Scale measurability and monotonicity of the Esscher-tilted scale yield measurable increasing translated densities.
-- source:
--   Exact decomposition of 1cc58853-df03-4323-883a-974f57a5e198.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_density_measurable_mono
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q x : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hW : IsQScale ψ q (W q))
    (hm : Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r))
    (hl : Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q))):
    let f : ℕ → ℝ → ℝ≥0∞ := fun n y => if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0
    (∀ n, Measurable (f n)) ∧ Monotone f := by
  sorry
