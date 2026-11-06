-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_inverse_eq_square_of_fourth_eq
-- name    : OAI.SevenEighths.InverseMoment.inverse_eq_square_of_fourth_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:42:07.98401+00:00
-- url     : https://prove2.me/theorems/66e636c1-d067-4ab3-8033-7233cfeec96e
-- title:
--   Inverse Moment: inverse eq square of fourth eq
-- statement:
--   The Inverse Moment construction uses the inverse eq square of fourth eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L59-L71
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L59-L71

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid

theorem OAI.SevenEighths.InverseMoment.inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by sorry
