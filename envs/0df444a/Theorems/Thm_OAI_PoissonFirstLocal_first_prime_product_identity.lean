-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_first_prime_product_identity
-- name    : OAI.PoissonFirstLocal.first_prime_product_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:23.953189+00:00
-- url     : https://prove2.me/theorems/4837c6f3-c7c2-426d-9f7e-9e53b996beb0
-- title:
--   Poisson First Local: first prime product identity
-- statement:
--   The Poisson First Local construction uses the first prime product identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L278-L298
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L278-L298

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

theorem OAI.PoissonFirstLocal.first_prime_product_identity
    (side : Bool) (P : Finset ℕ)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (n : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1) :
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
      (χ ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
      mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) := by sorry
