-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_cell_correction_norm_bound
-- name    : Kyprianou.Ch04.kw48_cell_correction_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:54:09.256709+00:00
-- url     : https://prove2.me/theorems/cdc64389-2d67-5b3f-a3b9-bc7fbf28b2df
-- title:
--   Single-cell complex correction norm bound
-- statement:
--   Single-cell complex correction norm bound.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_correction_cell
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_increment_norm_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The complex product correction is controlled by the log increment
and a deterministic real-part bound on the time horizon. -/

theorem Kyprianou.Ch04.kw48_cell_correction_norm_bound {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b T : NNReal) (hab : a ≤ b) (hbT : b ≤ T)
    (w : Ω) :
    ‖E L Psi alpha b w*(H L Psi alpha beta b w-H L Psi alpha beta a w)‖ ≤
      2*Real.exp (‖Psi alpha‖*(T:Real))*
        ‖G L Psi alpha beta b w-G L Psi alpha beta a w‖ := by sorry
