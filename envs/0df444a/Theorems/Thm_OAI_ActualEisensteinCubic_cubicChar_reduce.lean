-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_reduce
-- name    : OAI.ActualEisensteinCubic.cubicChar_reduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:24.381898+00:00
-- url     : https://prove2.me/theorems/a39bf8b8-8f50-44e8-8fb4-799f6e7a0ec6
-- title:
--   Actual Eisenstein Cubic: cubic Char reduce
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Char reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L578-L606
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L578-L606

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

theorem OAI.ActualEisensteinCubic.cubicChar_reduce (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    (Ideal.Quotient.mk P) (cubicChar P hgood x) =
      x ^ ((Nat.card (O ⧸ P) - 1) / 3) := by sorry
