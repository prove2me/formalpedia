-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_sum_first_prime_product_identity
-- name    : OAI.PoissonFirstLocal.sum_first_prime_product_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:34:53.045633+00:00
-- url     : https://prove2.me/theorems/f16ee732-d58e-4ace-ac02-f38d67f8c1f1
-- title:
--   Poisson First Local: sum first prime product identity
-- statement:
--   The Poisson First Local construction uses the sum first prime product identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L335-L347
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L335-L347

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

theorem OAI.PoissonFirstLocal.sum_first_prime_product_identity
    (S P : Finset ℕ) (side : Bool)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n *
      (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p (χ n))) =
    (∑ n ∈ S, a n *
      ((χ n ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
       mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p))) := by sorry
