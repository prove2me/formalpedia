-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_primitiveOnIdeals_iff_no_descent
-- name    : OAI.SevenEighths.FiniteConductor.primitiveOnIdeals_iff_no_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:39.454263+00:00
-- url     : https://prove2.me/theorems/4abdfff2-cb1a-4276-b7d3-93200589f8b0
-- title:
--   Finite Conductor: primitive On Ideals iff no descent
-- statement:
--   The Finite Conductor construction uses the primitive On Ideals iff no descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L75-L79
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L75-L79

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]

theorem OAI.SevenEighths.FiniteConductor.primitiveOnIdeals_iff_no_descent (χ : MulChar R ℂ) :
    IsPrimitiveOnIdeals χ ↔ ∀ I : Ideal R, I ≠ ⊥ → ¬ FactorsThroughIdeal χ I := by sorry
