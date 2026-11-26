-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_derivative_varianceHermite
-- name    : Malliavin.BrownianIteratedConstruction.derivative_varianceHermite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:24.879513+00:00
-- url     : https://prove2.me/theorems/f0f42685-54a5-473d-872f-0ff8530498b9
-- title:
--   Brownian Iterated Construction: derivative variance Hermite
-- statement:
--   Variance-parametrized Hermite polynomials form an Appell sequence.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L98-L116
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L98-L116

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.derivative_varianceHermite (variance : ℝ) (n : ℕ) :
    Polynomial.derivative (varianceHermite variance n) =
      Polynomial.C (n : ℝ) * varianceHermite variance (n - 1) := by sorry
