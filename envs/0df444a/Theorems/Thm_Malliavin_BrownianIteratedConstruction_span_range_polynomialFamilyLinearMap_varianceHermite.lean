-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_polynomialFamilyLinearMap_varianceHermite
-- name    : Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_varianceHermite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:31.423223+00:00
-- url     : https://prove2.me/theorems/656a0366-465e-4265-9c20-4c365405c8a7
-- title:
--   Brownian Iterated Construction: span range polynomial Family Linear Map variance Hermite
-- statement:
--   Generalized Hermite values have the same algebraic span as the prescribed monomial values.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L212-L218
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L212-L218

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

theorem Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_varianceHermite
    (variance : ℝ) (xpow : ℕ → M) :
    Submodule.span ℝ
        (Set.range fun n ↦ polynomialFamilyLinearMap xpow (varianceHermite variance n)) =
      Submodule.span ℝ (Set.range xpow) := by sorry
