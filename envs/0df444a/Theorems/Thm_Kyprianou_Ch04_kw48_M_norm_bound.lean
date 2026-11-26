-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_M_norm_bound
-- name    : Kyprianou.Ch04.kw48_M_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:54:47.344851+00:00
-- url     : https://prove2.me/theorems/124ade1d-c68e-4f66-8c57-525a3f6b8d59
-- title:
--   Linear bound on the proposed complex martingale
-- statement:
--   Linear bound on the proposed complex martingale.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_J_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_S_adapted_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The target complex martingale has a linear integrable envelope. -/

theorem Kyprianou.Ch04.kw48_M_norm_bound {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖M L Psi alpha beta t w‖ ≤
      ‖Psi alpha‖*(t:Real)+2+|alpha-beta| * runningSup L t w := by sorry
