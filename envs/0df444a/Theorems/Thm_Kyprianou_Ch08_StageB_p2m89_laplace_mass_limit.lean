-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_laplace_mass_limit
-- name    : Kyprianou.Ch08.StageB.p2m89_laplace_mass_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:14.43752+00:00
-- url     : https://prove2.me/theorems/026b705b-2537-4642-ac01-622c1fcdcbe4
-- title:
--   Nonnegative measure Laplace transforms converge to total mass
-- statement:
--   Monotone convergence along the decreasing positive sequence 1/(n+1).
-- source:
--   Reduction of 7b5acc12-33ec-419f-a633-a7295bab46be.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_laplace_mass_limit
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0) :
    Tendsto (fun n : ℕ => ∫⁻ y, ENNReal.ofReal
      (Real.exp (-(1 / ((n : ℝ) + 1)) * y)) ∂ν) atTop (𝓝 (ν univ)) := by
  sorry
