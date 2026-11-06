-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_reduce_unit
-- name    : OAI.ActualEisensteinCubic.sexticChar_reduce_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:19.434326+00:00
-- url     : https://prove2.me/theorems/c9616cfb-3e7a-497e-b4c6-6ae157b38869
-- title:
--   Actual Eisenstein Cubic: sextic Char reduce unit
-- statement:
--   The Actual Eisenstein Cubic construction uses the sextic Char reduce unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1337-L1382
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1337-L1382

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

theorem OAI.ActualEisensteinCubic.sexticChar_reduce_unit (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (u : (O ⧸ P)ˣ) :
    (Ideal.Quotient.mk P) (sexticChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((Nat.card (O ⧸ P) - 1) / 6) := by sorry
