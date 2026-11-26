-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
-- name    : Kyprianou.Ch04.kw48_Z_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:32:32.35516+00:00
-- url     : https://prove2.me/theorems/5fa6c8e5-f5d4-4364-95d6-5fb24b1f6a79
-- title:
--   Filtration measurability of complex Kella–Whitt factors
-- statement:
--   Filtration measurability of complex Kella–Whitt factors.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- All finite-time factors are measurable in the supplied filtration. -/

theorem Kyprianou.Ch04.kw48_Z_adapted {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) :
    Measurable[F t] (Z L alpha beta t) ∧
    Measurable[F t] (E L Psi alpha t) ∧
    Measurable[F t] (H L Psi alpha beta t) := by sorry
