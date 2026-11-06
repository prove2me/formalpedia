-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_mobius_char_exp_summable
-- name    : OAI.ShortDraftMellin.mobius_char_exp_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:52.572235+00:00
-- url     : https://prove2.me/theorems/4287a915-8a3d-4739-bff0-6ab4d767d146
-- title:
--   Short Draft Mellin: mobius char exp summable
-- statement:
--   The Short Draft Mellin construction uses the mobius char exp summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L511-L536
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L511-L536

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin

theorem OAI.ShortDraftMellin.mobius_char_exp_summable
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * t)) := by sorry
