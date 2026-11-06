-- Prove2me | Theorems.Thm_OAI_SevenEighths_EisensteinTheta_cosetTheta_hasSum
-- name    : OAI.SevenEighths.EisensteinTheta.cosetTheta_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:30.974009+00:00
-- url     : https://prove2.me/theorems/0a888037-f259-4b52-86d4-193c28134530
-- title:
--   Eisenstein Theta: coset Theta has Sum
-- statement:
--   The Eisenstein Theta construction uses the coset Theta has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EisensteinTheta.lean#L43-L76
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EisensteinTheta.lean#L43-L76

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

theorem OAI.SevenEighths.EisensteinTheta.cosetTheta_hasSum (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ))
      (∑ e : Fin 2, (parityPair a b L hL e).f t) := by sorry
