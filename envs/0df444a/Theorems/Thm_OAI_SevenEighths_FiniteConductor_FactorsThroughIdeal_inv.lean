-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_FactorsThroughIdeal_inv
-- name    : OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:22.840809+00:00
-- url     : https://prove2.me/theorems/93762bd4-fd7c-40e4-b9b4-d5fb443b2684
-- title:
--   Factors Through Ideal: inv
-- statement:
--   The Factors Through Ideal construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L86-L90
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L86-L90

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_IsPrimitiveOnIdeals_inv

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]

theorem OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.inv {χ : MulChar R ℂ} {I : Ideal R}
    (h : FactorsThroughIdeal χ I) : FactorsThroughIdeal χ⁻¹ I := by sorry
