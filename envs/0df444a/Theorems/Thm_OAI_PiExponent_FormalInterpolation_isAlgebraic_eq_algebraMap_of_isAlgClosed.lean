-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_isAlgebraic_eq_algebraMap_of_isAlgClosed
-- name    : OAI.PiExponent.FormalInterpolation.isAlgebraic_eq_algebraMap_of_isAlgClosed
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:19:54.950991+00:00
-- url     : https://prove2.me/theorems/9a04d30b-dfbb-430a-be09-54b7f1f5fbc2
-- title:
--   Algebraic elements over an algebraically closed field are constants
-- statement:
--   If E is a field extension of the complex numbers and x in E is algebraic over C, then x lies in the image of the structure map C → E, since C is algebraically closed.
-- source:
--   Mathlib IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic.

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic

theorem OAI.PiExponent.FormalInterpolation.isAlgebraic_eq_algebraMap_of_isAlgClosed
    {E : Type} [Field E] [Algebra Complex E] (x : E) (hx : IsAlgebraic Complex x) :
    ∃ a : Complex, x = algebraMap Complex E a := by sorry
