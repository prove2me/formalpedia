-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_finite_expansion_energy
-- name    : OAI.SevenEighths.InverseMoment.finite_expansion_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:54.940238+00:00
-- url     : https://prove2.me/theorems/53f45a63-7b3c-4bb0-a6cd-585b63ecc3a4
-- title:
--   Inverse Moment: finite expansion energy
-- statement:
--   The Inverse Moment construction uses the finite expansion energy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Fibers.lean#L91-L134
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Fibers.lean#L91-L134

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section

theorem OAI.SevenEighths.InverseMoment.finite_expansion_energy {κ ι : Type*} [DecidableEq ι]
    (rows : Finset κ) (terms : Finset ι) (active : κ → Finset ι)
    (w F : κ → ι → ℂ) (C : ℝ)
    (hsub : ∀ k ∈ rows, active k ⊆ terms)
    (hw : ∀ k ∈ rows, ∀ i ∈ active k, ‖w k i‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((active k).card : ℝ) ≤ C) :
    (∑ k ∈ rows, ‖∑ i ∈ active k, w k i * F k i‖ ^ 2) ≤
      C * ∑ i ∈ terms, ∑ k ∈ rows, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by sorry
