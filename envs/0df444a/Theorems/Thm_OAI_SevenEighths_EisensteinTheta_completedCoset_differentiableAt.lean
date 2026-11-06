-- Prove2me | Theorems.Thm_OAI_SevenEighths_EisensteinTheta_completedCoset_differentiableAt
-- name    : OAI.SevenEighths.EisensteinTheta.completedCoset_differentiableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:39:33.923863+00:00
-- url     : https://prove2.me/theorems/07c6e31d-22eb-478d-9faa-f56de02111ae
-- title:
--   Eisenstein Theta: completed Coset differentiable At
-- statement:
--   The Eisenstein Theta construction uses the completed Coset differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EisensteinTheta.lean#L138-L144
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EisensteinTheta.lean#L138-L144

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.EisensteinTheta
open ThetaProduct

theorem OAI.SevenEighths.EisensteinTheta.completedCoset_differentiableAt (a b L : ℝ) (hL : 0 < L)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (completedCoset a b L hL) s := by sorry
