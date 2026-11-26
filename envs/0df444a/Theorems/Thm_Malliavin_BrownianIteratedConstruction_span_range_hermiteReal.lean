-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_hermiteReal
-- name    : Malliavin.BrownianIteratedConstruction.span_range_hermiteReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:15.660567+00:00
-- url     : https://prove2.me/theorems/3044a282-1b53-4927-9db6-84bcdbe696d6
-- title:
--   Brownian Iterated Construction: span range hermite Real
-- statement:
--   The real Hermite polynomials algebraically span every real polynomial.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L75-L77
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L75-L77

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.span_range_hermiteReal :
    Submodule.span ℝ (Set.range hermiteReal) = ⊤ := by sorry
