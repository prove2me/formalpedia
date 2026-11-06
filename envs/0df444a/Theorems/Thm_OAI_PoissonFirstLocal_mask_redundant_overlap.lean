-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_mask_redundant_overlap
-- name    : OAI.PoissonFirstLocal.mask_redundant_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:47.694994+00:00
-- url     : https://prove2.me/theorems/91ad94f0-6000-4bc0-ba83-65acc1b02026
-- title:
--   Poisson First Local: mask redundant overlap
-- statement:
--   The Poisson First Local construction uses the mask redundant overlap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L300-L319
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L300-L319

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

theorem OAI.PoissonFirstLocal.mask_redundant_overlap
    (n J B₀ b₀ m : ℕ) (χ : MulChar (ZMod n) ℂ)
    (hB : B₀ ∣ b₀) (hb : b₀ ∣ (B₀ * J) ^ m) :
    (χ (J : ZMod n)) ^ 4 * mask n B₀ =
      (χ (J : ZMod n)) ^ 4 * mask n b₀ := by sorry
