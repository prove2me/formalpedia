-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_product
-- name    : OAI.ActualEisensteinCubic.cubicJacobi_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:51.583237+00:00
-- url     : https://prove2.me/theorems/f404ca8f-1e86-47dc-983d-dd5653a1f7ac
-- title:
--   Actual Eisenstein Cubic: cubic Jacobi product
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Jacobi product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L689-L724
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L689-L724

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
open Finset Complex
open OAI.ActualEisensteinCubic
open NumberField

theorem OAI.ActualEisensteinCubic.cubicJacobi_product (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ =
        (Nat.card (O ⧸ P) : O) := by sorry
