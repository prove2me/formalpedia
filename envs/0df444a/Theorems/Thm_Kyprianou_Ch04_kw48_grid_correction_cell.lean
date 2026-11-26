-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_grid_correction_cell
-- name    : Kyprianou.Ch04.kw48_grid_correction_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:12.40724+00:00
-- url     : https://prove2.me/theorems/41e84fb6-b90a-5c7f-a15c-39dc7b78ca29
-- title:
--   Exact complex logarithmic grid correction identity
-- statement:
--   Exact complex logarithmic grid correction identity.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_product
import Theorems.Thm_Kyprianou_Ch04_kw48_exponential_cell_product
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact complex product correction expressed in terms of the log-weight. -/

theorem Kyprianou.Ch04.kw48_grid_correction_cell {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b : NNReal) (w : Ω) :
    E L Psi alpha b w*(H L Psi alpha beta b w-H L Psi alpha beta a w) =
      Z L alpha beta b w*
        (1-Complex.exp (-(G L Psi alpha beta b w-G L Psi alpha beta a w))) := by sorry
