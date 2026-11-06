-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_idealCRT
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_idealCRT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:38:58.270458+00:00
-- url     : https://prove2.me/theorems/7c6b2c6d-5363-4f52-89e3-ab84c21ffd5b
-- title:
--   Centered Moment Correlation: full Correlation ideal CRT
-- statement:
--   The Centered Moment Correlation construction uses the full Correlation ideal CRT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L86-L98
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L86-L98

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

theorem OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_idealCRT {S ι : Type*} [CommRing S] [Fintype ι]
    (I : ι → Ideal S) (hI : Pairwise (Function.onFun IsCoprime I))
    [Fintype (S ⧸ ⨅ i, I i)] [∀ i, Fintype (S ⧸ I i)]
    (u v k : S ⧸ ⨅ i, I i) (f g : ∀ i, S ⧸ I i → ℂ) :
    let e := Ideal.quotientInfRingEquivPiQuotient I hI
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (e x i)) (fun y => ∏ i, g i (e y i)) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (f i) (g i) (e k i) := by sorry
