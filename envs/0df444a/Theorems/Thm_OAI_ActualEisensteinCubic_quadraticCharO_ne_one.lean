-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_quadraticCharO_ne_one
-- name    : OAI.ActualEisensteinCubic.quadraticCharO_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:20:10.316097+00:00
-- url     : https://prove2.me/theorems/7dade2e3-7f06-4f0d-b80d-cccd1f71b10a
-- title:
--   Actual Eisenstein Cubic: quadratic Char O ne one
-- statement:
--   The Actual Eisenstein Cubic construction uses the quadratic Char O ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1278-L1285
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1278-L1285

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

theorem OAI.ActualEisensteinCubic.quadraticCharO_ne_one (P : Ideal O) [P.IsMaximal]
    (hchar : ringChar (O ⧸ P) ≠ 2) : quadraticCharO P ≠ 1 := by sorry
