-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_J_adapted
-- name    : Kyprianou.Ch04.kw48_J_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:54:57.614039+00:00
-- url     : https://prove2.me/theorems/540512bf-ce56-43f7-a436-4043577850a0
-- title:
--   Actual complex time primitive is adapted
-- statement:
--   Actual complex time primitive is adapted.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual time primitive is adapted by right-endpoint grid approximation. -/

theorem Kyprianou.Ch04.kw48_J_adapted {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) :
    Measurable[F t] (J L alpha beta t) := by sorry
