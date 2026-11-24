-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_density_pointwise_limit
-- name    : Kyprianou.Ch08.StageB.p2m89_density_pointwise_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:24:44.319822+00:00
-- url     : https://prove2.me/theorems/6bf5ed6d-88d6-4a14-a579-2c2552810144
-- title:
--   Pointwise limit of translated densities
-- statement:
--   Moving support eventually includes every destination; continuity of multiplication and ENNReal.ofReal gives the pointwise limit.
-- source:
--   Exact decomposition of 1cc58853-df03-4323-883a-974f57a5e198.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_density_pointwise_limit
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q x : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hW : IsQScale ψ q (W q))
    (hm : Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r))
    (hl : Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q))):
    let f : ℕ → ℝ → ℝ≥0∞ := fun n y => if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0
    ∀ y : ℝ, Tendsto (fun n : ℕ => f n y) atTop
      (𝓝 (ENNReal.ofReal (unrestrictedPotentialDensity ψ q (W q) (y-x)))) := by
  sorry
