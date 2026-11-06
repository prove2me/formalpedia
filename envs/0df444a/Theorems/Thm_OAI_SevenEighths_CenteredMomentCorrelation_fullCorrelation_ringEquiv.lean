-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_ringEquiv
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_ringEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:05.296592+00:00
-- url     : https://prove2.me/theorems/172bb0cb-2c00-49bc-b129-77b245aeb61d
-- title:
--   Centered Moment Correlation: full Correlation ring Equiv
-- statement:
--   The Centered Moment Correlation construction uses the full Correlation ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L12-L23
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/CRT.lean#L12-L23

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

theorem OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_ringEquiv (e : A ≃+* B) (u v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f (e x)) (fun y => g (e y)) k =
      fullCorrelation (fun x => e v * x) (fun y => e u * y) f g (e k) := by sorry
