-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_eq_tuple_sum
-- name    : OAI.SevenEighths.InverseMoment.primeMark_eq_tuple_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:41:35.131116+00:00
-- url     : https://prove2.me/theorems/b680596e-556c-4f3d-b71d-f539552fa10c
-- title:
--   Inverse Moment: prime Mark eq tuple sum
-- statement:
--   The Inverse Moment construction uses the prime Mark eq tuple sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L26-L30
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L26-L30

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

theorem OAI.SevenEighths.InverseMoment.primeMark_eq_tuple_sum (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ p ∈ I.pi L,
      ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0 := by sorry
