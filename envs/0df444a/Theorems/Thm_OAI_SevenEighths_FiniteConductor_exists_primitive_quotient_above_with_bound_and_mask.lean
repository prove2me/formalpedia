-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_quotient_above_with_bound_and_mask
-- name    : OAI.SevenEighths.FiniteConductor.exists_primitive_quotient_above_with_bound_and_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:46.354411+00:00
-- url     : https://prove2.me/theorems/4517c493-1c80-4d28-8c50-b3294668ef62
-- title:
--   Finite Conductor: exists primitive quotient above with bound and mask
-- statement:
--   The Finite Conductor construction uses the exists primitive quotient above with bound and mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L95-L105
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L95-L105

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]

theorem OAI.SevenEighths.FiniteConductor.exists_primitive_quotient_above_with_bound_and_mask
    (χ : MulChar R ℂ) (J : Ideal R) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by sorry
