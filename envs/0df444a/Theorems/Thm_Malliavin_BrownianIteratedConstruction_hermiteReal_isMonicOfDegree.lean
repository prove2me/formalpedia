-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_hermiteReal_isMonicOfDegree
-- name    : Malliavin.BrownianIteratedConstruction.hermiteReal_isMonicOfDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:54.976797+00:00
-- url     : https://prove2.me/theorems/39d55ce3-9b0d-5389-a1a8-348df0ca72c7
-- title:
--   Brownian Iterated Construction: hermite Real is Monic Of Degree
-- statement:
--   Real Hermite polynomials are monic of their indexed degree.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L30-L35
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L30-L35

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.hermiteReal_isMonicOfDegree (n : ℕ) :
    Polynomial.IsMonicOfDegree (hermiteReal n) n := by sorry
