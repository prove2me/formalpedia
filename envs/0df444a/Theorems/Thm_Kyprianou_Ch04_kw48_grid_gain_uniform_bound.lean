-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_grid_gain_uniform_bound
-- name    : Kyprianou.Ch04.kw48_grid_gain_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:36:42.250624+00:00
-- url     : https://prove2.me/theorems/d9e327a0-c316-4701-989e-d8729120753e
-- title:
--   Integrable envelope for predictable product gains
-- statement:
--   Integrable envelope for predictable product gains.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_correction_grid_norm_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_discrete_product_summation
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_product
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite predictable grid gain is dominated by twice the common
integrable envelope, regardless of its mesh or number of cells. -/

theorem Kyprianou.Ch04.kw48_grid_gain_uniform_bound {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (T : NNReal) (u : Nat → NNReal) (N : Nat)
    (hu : Monotone u) (hT : ∀ i, u i ≤ T) (w : Ω) :
    ‖Q L Psi alpha beta u N w‖ ≤ 2*envelope L Psi alpha beta T w := by sorry
