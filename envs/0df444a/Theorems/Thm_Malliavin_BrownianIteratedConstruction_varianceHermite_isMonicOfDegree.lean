-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_varianceHermite_isMonicOfDegree
-- name    : Malliavin.BrownianIteratedConstruction.varianceHermite_isMonicOfDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:25.105599+00:00
-- url     : https://prove2.me/theorems/f9cb08ae-004c-5601-be72-4b922397a8c2
-- title:
--   Brownian Iterated Construction: variance Hermite is Monic Of Degree
-- statement:
--   Every variance-parametrized Hermite polynomial is monic of its indexed degree.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L119-L134
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L119-L134

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.varianceHermite_isMonicOfDegree (variance : ℝ) (n : ℕ) :
    Polynomial.IsMonicOfDegree (varianceHermite variance n) n := by sorry
