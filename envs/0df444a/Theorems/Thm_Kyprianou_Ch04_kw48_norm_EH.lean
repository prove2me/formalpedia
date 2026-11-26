-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_norm_EH
-- name    : Kyprianou.Ch04.kw48_norm_EH
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:32:14.889527+00:00
-- url     : https://prove2.me/theorems/2e4670ea-b829-575e-a8e5-51251f586491
-- title:
--   Deterministic modulus of complex exponential factors
-- statement:
--   Deterministic modulus of complex exponential factors.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Both exponential factors have deterministic modulus. -/

theorem Kyprianou.Ch04.kw48_norm_EH {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖E L Psi alpha t w‖ = Real.exp ((t:Real)*(Psi alpha).re) ∧
    ‖H L Psi alpha beta t w‖ = Real.exp (-(t:Real)*(Psi alpha).re) := by sorry
