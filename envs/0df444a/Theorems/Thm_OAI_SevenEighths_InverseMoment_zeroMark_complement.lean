-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_zeroMark_complement
-- name    : OAI.SevenEighths.InverseMoment.zeroMark_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:00:03.350207+00:00
-- url     : https://prove2.me/theorems/e2486aa8-6305-4612-a411-09b6921f3d0a
-- title:
--   Inverse Moment: zero Mark complement
-- statement:
--   The Inverse Moment construction uses the zero Mark complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L31-L36
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L31-L36

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]
omit [Fintype F]

theorem OAI.SevenEighths.InverseMoment.zeroMark_complement (x : F) :
    zeroMark x = 1 - (1 : MulChar F ℂ) x := by sorry
