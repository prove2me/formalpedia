-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_primeSlot_norm_le
-- name    : OAI.SevenEighths.InverseMoment.primeSlot_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:14.549043+00:00
-- url     : https://prove2.me/theorems/6d749e12-b8d2-42ae-af7a-d4ec38bb4188
-- title:
--   Inverse Moment: prime Slot norm le
-- statement:
--   The Inverse Moment construction uses the prime Slot norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L65-L73
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Marks.lean#L65-L73

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

theorem OAI.SevenEighths.InverseMoment.primeSlot_norm_le (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by sorry
