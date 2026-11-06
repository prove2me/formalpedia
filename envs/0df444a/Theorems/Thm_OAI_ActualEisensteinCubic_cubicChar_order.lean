-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_order
-- name    : OAI.ActualEisensteinCubic.cubicChar_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:25.572473+00:00
-- url     : https://prove2.me/theorems/2d512e8b-b824-4fed-ba1e-351ce0c31edd
-- title:
--   Actual Eisenstein Cubic: cubic Char order
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Char order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L648-L654
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L648-L654

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

theorem OAI.ActualEisensteinCubic.cubicChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : orderOf (cubicChar P hgood) = 3 := by sorry
