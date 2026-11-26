-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_varianceHermite
-- name    : Malliavin.BrownianIteratedConstruction.span_range_varianceHermite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:43.616803+00:00
-- url     : https://prove2.me/theorems/671c1596-178b-548d-89ac-1f9fa1c186f8
-- title:
--   Brownian Iterated Construction: span range variance Hermite
-- statement:
--   For every variance parameter, generalized Hermite polynomials span `ℝ[X]`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L137-L140
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L137-L140

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.span_range_varianceHermite (variance : ℝ) :
    Submodule.span ℝ (Set.range (varianceHermite variance)) = ⊤ := by sorry
