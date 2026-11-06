-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_quotient
-- name    : OAI.SevenEighths.FiniteConductor.exists_primitive_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:13:30.667088+00:00
-- url     : https://prove2.me/theorems/74a49080-982b-4fd3-8a01-f461e968872d
-- title:
--   Finite Conductor: exists primitive quotient
-- statement:
--   The Finite Conductor construction uses the exists primitive quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L105-L144
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L105-L144

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

theorem OAI.SevenEighths.FiniteConductor.exists_primitive_quotient (χ : MulChar R ℂ) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by sorry
