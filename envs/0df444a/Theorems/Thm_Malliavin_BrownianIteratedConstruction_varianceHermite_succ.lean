-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_varianceHermite_succ
-- name    : Malliavin.BrownianIteratedConstruction.varianceHermite_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:00.710425+00:00
-- url     : https://prove2.me/theorems/cf49c8a2-d082-4770-b5f2-c79887768197
-- title:
--   Brownian Iterated Construction: variance Hermite succ
-- statement:
--   Unified successor recurrence for variance-parametrized Hermite polynomials.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L89-L95
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L89-L95

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.varianceHermite_succ (variance : ℝ) (n : ℕ) :
    varianceHermite variance (n + 1) =
      Polynomial.X * varianceHermite variance n -
        Polynomial.C (variance * n) * varianceHermite variance (n - 1) := by sorry
