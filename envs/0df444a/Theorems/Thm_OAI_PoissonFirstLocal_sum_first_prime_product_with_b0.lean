-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_sum_first_prime_product_with_b0
-- name    : OAI.PoissonFirstLocal.sum_first_prime_product_with_b0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:34:56.544472+00:00
-- url     : https://prove2.me/theorems/c1806236-daa4-4d81-9b61-f1db82c32099
-- title:
--   Poisson First Local: sum first prime product with b0
-- statement:
--   The Poisson First Local construction uses the sum first prime product with b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L349-L366
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L349-L366

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.PoissonFirstLocal
open scoped Classical

theorem OAI.PoissonFirstLocal.sum_first_prime_product_with_b0
    (S P : Finset ℕ) (side : Bool)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ)
    (b₀ m : ℕ)
    (hB : (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) ∣ b₀)
    (hb : b₀ ∣
      ((∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) *
       (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p)) ^ m) :
    (∑ n ∈ S, a n *
      (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p (χ n))) =
    (∑ n ∈ S, a n *
      ((χ n ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
       mask n b₀)) := by sorry
