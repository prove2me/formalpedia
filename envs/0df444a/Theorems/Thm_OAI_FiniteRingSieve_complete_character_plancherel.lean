-- Prove2me | Theorems.Thm_OAI_FiniteRingSieve_complete_character_plancherel
-- name    : OAI.FiniteRingSieve.complete_character_plancherel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:29:51.621817+00:00
-- url     : https://prove2.me/theorems/683545b9-f6ce-4d6b-add3-349dd9d5b716
-- title:
--   Finite Ring Sieve: complete character plancherel
-- statement:
--   The Finite Ring Sieve construction uses the complete character plancherel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L213-L254
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L213-L254

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
attribute [local instance] OAI.FiniteRingSieve.logProfilesFintypeMulChar
attribute [local instance] logProfilesFintypeMulChar

theorem OAI.FiniteRingSieve.complete_character_plancherel (a : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖∑ u : Rˣ, a u * χ (u : R)‖ ^ 2) =
      (Fintype.card Rˣ : ℝ) * ∑ u : Rˣ, ‖a u‖ ^ 2 := by sorry
