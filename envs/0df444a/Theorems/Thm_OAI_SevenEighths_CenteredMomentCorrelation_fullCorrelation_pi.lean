-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_pi
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:04.975625+00:00
-- url     : https://prove2.me/theorems/07ccd516-cfee-4631-b34a-2a990a05d4f3
-- title:
--   Centered Moment Correlation: full Correlation pi
-- statement:
--   The Centered Moment Correlation construction uses the full Correlation pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L55-L84
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L55-L84

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

theorem OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_pi {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]
    (u v k : ∀ i, R i) (f g : ∀ i, R i → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (fun x => v i * x) (fun y => u i * y) (f i) (g i) (k i) := by sorry
