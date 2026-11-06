-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicSieve_rectangular_block_energy_le
-- name    : OAI.SevenEighths.CubicSieve.rectangular_block_energy_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:17.367145+00:00
-- url     : https://prove2.me/theorems/ac1a5cc3-4778-4961-9931-bc74f67d07ad
-- title:
--   Cubic Sieve: rectangular block energy le
-- statement:
--   The Cubic Sieve construction uses the rectangular block energy le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Blocks.lean#L27-L72
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Blocks.lean#L27-L72

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Blocks
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]

theorem OAI.SevenEighths.CubicSieve.rectangular_block_energy_le
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef mask : n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ j, ‖mask j‖ ≤ 1) :
    (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
      min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by sorry
