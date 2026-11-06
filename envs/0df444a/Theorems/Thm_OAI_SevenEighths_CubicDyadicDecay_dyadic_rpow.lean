-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicDyadicDecay_dyadic_rpow
-- name    : OAI.SevenEighths.CubicDyadicDecay.dyadic_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:14.99622+00:00
-- url     : https://prove2.me/theorems/dd00a3cc-4dc8-4b59-ac44-a13c1cdcf9de
-- title:
--   Cubic Dyadic Decay: dyadic rpow
-- statement:
--   The Cubic Dyadic Decay construction uses the dyadic rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L19-L22
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean#L19-L22

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

theorem OAI.SevenEighths.CubicDyadicDecay.dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by sorry
