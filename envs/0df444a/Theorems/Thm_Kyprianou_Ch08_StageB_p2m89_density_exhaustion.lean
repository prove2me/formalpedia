-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_density_exhaustion
-- name    : Kyprianou.Ch08.StageB.p2m89_density_exhaustion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:18:52.732871+00:00
-- url     : https://prove2.me/theorems/1cc58853-df03-4323-883a-974f57a5e198
-- title:
--   Translated density converges to unrestricted density
-- statement:
--   Use monotone convergence for the nonnegative translated densities; the indicator exhausts the real line and the tilted scale converges to the inverse derivative.
-- source:
--   Kyprianou (2006), Corollary 8.9; corrected occupation identity 33cf8321-6b73-409d-84cc-a8da6fcb2949.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_density_exhaustion
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q x : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hW : IsQScale ψ q (W q))
    (hm : Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r))
    (hl : Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q))) :
    Tendsto (fun n : ℕ => (∫⁻ y in A, if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0)) atTop
      (𝓝 ((volume.withDensity (fun y : ℝ => ENNReal.ofReal
        (unrestrictedPotentialDensity ψ q (W q) (y - x)))) A)) := by
  sorry
