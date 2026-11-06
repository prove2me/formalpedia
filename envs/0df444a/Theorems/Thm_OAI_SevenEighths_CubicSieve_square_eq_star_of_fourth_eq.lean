-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicSieve_square_eq_star_of_fourth_eq
-- name    : OAI.SevenEighths.CubicSieve.square_eq_star_of_fourth_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:40:55.214548+00:00
-- url     : https://prove2.me/theorems/813add01-93e2-4d4f-ac73-2f25c8b5beac
-- title:
--   Cubic Sieve: square eq star of fourth eq
-- statement:
--   The Cubic Sieve construction uses the square eq star of fourth eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Algebra.lean#L14-L25
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Algebra.lean#L14-L25

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Algebra
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem OAI.SevenEighths.CubicSieve.square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by sorry
