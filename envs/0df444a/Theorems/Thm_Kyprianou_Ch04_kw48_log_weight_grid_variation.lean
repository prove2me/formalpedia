-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_log_weight_grid_variation
-- name    : Kyprianou.Ch04.kw48_log_weight_grid_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:41:25.673196+00:00
-- url     : https://prove2.me/theorems/b92c81d5-5c8f-4f50-a8fc-6912489dee20
-- title:
--   Total variation bound for the complex logarithmic predictable weight
-- statement:
--   Total variation bound for the complex logarithmic predictable weight.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Total grid variation of the complex logarithmic weight is bounded
by the sum of record and elapsed-time variations. -/

theorem Kyprianou.Ch04.kw48_log_weight_grid_variation {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (w : Ω)
    (u : Nat → NNReal) (N : Nat) (hu : Monotone u) :
    (∑ i ∈ Finset.range N,
      ‖G L Psi alpha beta (u (i+1)) w-G L Psi alpha beta (u i) w‖) ≤
      |beta-alpha| * (runningSup L (u N) w-runningSup L (u 0) w) +
        ‖Psi alpha‖ * ((u N:Real)-(u 0:Real)) := by sorry
