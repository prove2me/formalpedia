-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_residual_lists
-- name    : OAI.SevenEighths.InverseMoment.primeMark_residual_lists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:41:52.350196+00:00
-- url     : https://prove2.me/theorems/2cfc642b-b54f-4996-b195-fcac6ca80b34
-- title:
--   Inverse Moment: prime Mark residual lists
-- statement:
--   The Inverse Moment construction uses the prime Mark residual lists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L57-L63
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L57-L63

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
omit [DecidableEq σ]

theorem OAI.SevenEighths.InverseMoment.primeMark_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by sorry
