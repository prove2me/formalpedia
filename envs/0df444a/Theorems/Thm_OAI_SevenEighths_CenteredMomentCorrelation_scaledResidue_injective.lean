-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_injective
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:40.681196+00:00
-- url     : https://prove2.me/theorems/39e79f46-0e87-49ba-ad2d-c416b0a9ec51
-- title:
--   Centered Moment Correlation: scaled Residue injective
-- statement:
--   The Centered Moment Correlation construction uses the scaled Residue injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/FullCorrelation.lean#L151-L161
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/FullCorrelation.lean#L151-L161

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
variable [IsDomain A]

theorem OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_injective (d a m : A) (hm : m = d * a) (ha : a ≠ 0) :
    Function.Injective (scaledResidue d a m hm) := by sorry
