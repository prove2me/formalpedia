-- Prove2me | Theorems.Thm_OAI_SevenEighths_EulerFactors_differentiable_deletedProduct
-- name    : OAI.SevenEighths.EulerFactors.differentiable_deletedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:51:54.610719+00:00
-- url     : https://prove2.me/theorems/e260b10d-989e-487f-9a55-7ccc6606c043
-- title:
--   Euler Factors: differentiable deleted Product
-- statement:
--   The Euler Factors construction uses the differentiable deleted Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EulerFactors.lean#L47-L63
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EulerFactors.lean#L47-L63

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

theorem OAI.SevenEighths.EulerFactors.differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by sorry
