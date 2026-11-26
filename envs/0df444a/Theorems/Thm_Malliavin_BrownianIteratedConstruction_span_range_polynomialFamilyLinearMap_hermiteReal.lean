-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_polynomialFamilyLinearMap_hermiteReal
-- name    : Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_hermiteReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:55.014037+00:00
-- url     : https://prove2.me/theorems/28485dcc-92ed-4eed-82e0-2544f168a77d
-- title:
--   Brownian Iterated Construction: span range polynomial Family Linear Map hermite Real
-- statement:
--   Applying any linear map prescribed on monomials to the Hermite family does not change the
--   algebraic span of its values.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L204-L209
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L204-L209

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
variable {M : Type*} [AddCommMonoid M] [Module ℝ M]

theorem Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_hermiteReal (xpow : ℕ → M) :
    Submodule.span ℝ
        (Set.range fun n ↦ polynomialFamilyLinearMap xpow (hermiteReal n)) =
      Submodule.span ℝ (Set.range xpow) := by sorry
