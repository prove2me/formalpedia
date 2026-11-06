-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_crtCharacter_apply
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.crtCharacter_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:39:07.258482+00:00
-- url     : https://prove2.me/theorems/63b0ae5e-ac68-4aab-9733-f51cc3852f04
-- title:
--   Centered Moment Correlation: crt Character apply
-- statement:
--   The Centered Moment Correlation construction uses the crt Character apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L116-L118
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L116-L118

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_CRT
set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem OAI.SevenEighths.CenteredMomentCorrelation.crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := by sorry

attribute [defeq] OAI.SevenEighths.CenteredMomentCorrelation.crtCharacter_apply
