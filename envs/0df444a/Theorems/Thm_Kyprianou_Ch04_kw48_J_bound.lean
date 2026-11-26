-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_J_bound
-- name    : Kyprianou.Ch04.kw48_J_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:46:17.137623+00:00
-- url     : https://prove2.me/theorems/d8d89bd5-6f5f-4db6-887b-bfb10a3e3784
-- title:
--   Finite-horizon norm bound for the complex time integral
-- statement:
--   Finite-horizon norm bound for the complex time integral.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The complex time primitive is bounded in norm by elapsed time. -/

theorem Kyprianou.Ch04.kw48_J_bound {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖J L alpha beta t w‖ ≤ (t:Real) := by sorry
