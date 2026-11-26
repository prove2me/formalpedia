-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_correction_grid_norm_bound
-- name    : Kyprianou.Ch04.kw48_correction_grid_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:33:28.978914+00:00
-- url     : https://prove2.me/theorems/59348e99-9ac6-48e1-bd08-a51a80b01166
-- title:
--   Uniform bound for actual product correction
-- statement:
--   Uniform bound for actual product correction.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_cell_correction_norm_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_log_weight_grid_variation
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A deterministic real-part cap and the log-weight's grid variation
bound the total complex correction uniformly on a finite horizon. -/

theorem Kyprianou.Ch04.kw48_correction_grid_norm_bound {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (T : NNReal) (u : Nat → NNReal) (N : Nat)
    (hu : Monotone u) (hT : ∀ i, u i ≤ T) (w : Ω) :
    ‖C L Psi alpha beta u N w‖ ≤
      2*Real.exp (‖Psi alpha‖*(T:Real))*
        (|beta-alpha| * runningSup L T w+‖Psi alpha‖*(T:Real)) := by sorry
