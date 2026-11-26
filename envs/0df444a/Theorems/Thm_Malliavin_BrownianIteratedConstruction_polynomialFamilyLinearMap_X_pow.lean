-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
-- name    : Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:30.977972+00:00
-- url     : https://prove2.me/theorems/402e7b99-b659-5ea9-be61-15cb89a8c227
-- title:
--   Brownian Iterated Construction: polynomial Family Linear Map X pow
-- statement:
--   `polynomialFamilyLinearMap` has the prescribed value on every monomial.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L151-L156
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L151-L156

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

theorem Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow (xpow : ℕ → M) (n : ℕ) :
    polynomialFamilyLinearMap xpow (Polynomial.X ^ n) = xpow n := by sorry
