-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_polynomialFamilyLinearMap_of_span_eq_top
-- name    : Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_of_span_eq_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:19.354835+00:00
-- url     : https://prove2.me/theorems/a03b68be-9e2e-4612-988a-277404e4d53b
-- title:
--   Brownian Iterated Construction: span range polynomial Family Linear Map of span eq top
-- statement:
--   A polynomial family spanning `ℝ[X]` continues to span the prescribed monomial values after
--   applying `polynomialFamilyLinearMap`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L160-L200
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L160-L200

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

theorem Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_of_span_eq_top
    (p : ℕ → Polynomial ℝ) (hp : Submodule.span ℝ (Set.range p) = ⊤)
    (xpow : ℕ → M) :
    Submodule.span ℝ (Set.range fun n ↦ polynomialFamilyLinearMap xpow (p n)) =
      Submodule.span ℝ (Set.range xpow) := by sorry
