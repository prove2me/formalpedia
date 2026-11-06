-- Prove2me | Theorems.Thm_OAI_PoissonChildCRT_mask_mul
-- name    : OAI.PoissonChildCRT.mask_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:33.809477+00:00
-- url     : https://prove2.me/theorems/72f8f083-ffe8-48b1-b44c-ede3b1c450cd
-- title:
--   Poisson Child CRT: mask mul
-- statement:
--   The Poisson Child CRT construction uses the mask mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L86-L103
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L86-L103

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
open OAI.PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)

theorem OAI.PoissonChildCRT.mask_mul (n a b : ℕ) :
    mask n (a * b) = mask n a * mask n b := by sorry
