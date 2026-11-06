-- Prove2me | Theorems.Thm_OAI_SevenEighths_EulerFactors_deletedProduct_ne_zero
-- name    : OAI.SevenEighths.EulerFactors.deletedProduct_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:22:21.391245+00:00
-- url     : https://prove2.me/theorems/24b14d0b-7eba-4fe9-b42f-099116c3bdc5
-- title:
--   Euler Factors: deleted Product ne zero
-- statement:
--   The Euler Factors construction uses the deleted Product ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EulerFactors.lean#L40-L45
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EulerFactors.lean#L40-L45

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_EulerFactors
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.EulerFactors
noncomputable section

theorem OAI.SevenEighths.EulerFactors.deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by sorry
