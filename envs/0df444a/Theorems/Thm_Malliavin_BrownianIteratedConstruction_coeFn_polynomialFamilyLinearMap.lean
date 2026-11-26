-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_polynomialFamilyLinearMap
-- name    : Malliavin.BrownianIteratedConstruction.coeFn_polynomialFamilyLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:29.788717+00:00
-- url     : https://prove2.me/theorems/2a5b1628-b796-483a-9b45-37eb24f7c413
-- title:
--   Brownian Iterated Construction: coe Fn polynomial Family Linear Map
-- statement:
--   If the prescribed monomial values represent powers of one random variable, then the induced
--   linear map represents pointwise polynomial evaluation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L224-L243
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L224-L243

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
variable {W : Type*} [MeasurableSpace W] {P : Measure W}

theorem Malliavin.BrownianIteratedConstruction.coeFn_polynomialFamilyLinearMap
    (xpow : ℕ → Lp ℝ 2 P) (X : W → ℝ)
    (hxpow : ∀ n, (xpow n : W → ℝ) =ᵐ[P] fun w ↦ X w ^ n)
    (p : Polynomial ℝ) :
    (polynomialFamilyLinearMap xpow p : W → ℝ) =ᵐ[P]
      fun w ↦ p.eval (X w) := by sorry
