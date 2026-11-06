-- Prove2me | Theorems.Thm_OAI_PoissonChildCRT_mask_absorb_inv_char
-- name    : OAI.PoissonChildCRT.mask_absorb_inv_char
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:46.337195+00:00
-- url     : https://prove2.me/theorems/5f0e9642-cf31-48b4-900a-a9a7651bbeda
-- title:
--   Poisson Child CRT: mask absorb inv char
-- statement:
--   The Poisson Child CRT construction uses the mask absorb inv char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L115-L123
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L115-L123

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

theorem OAI.PoissonChildCRT.mask_absorb_inv_char (e : ℕ) :
    mask n e * (χ (e : ZMod n))⁻¹ = (χ (e : ZMod n))⁻¹ := by sorry
