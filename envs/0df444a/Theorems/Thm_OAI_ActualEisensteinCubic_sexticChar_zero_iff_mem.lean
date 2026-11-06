-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_zero_iff_mem
-- name    : OAI.ActualEisensteinCubic.sexticChar_zero_iff_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:24.055145+00:00
-- url     : https://prove2.me/theorems/0c0e197e-4674-4229-b5f7-aa9985caf61e
-- title:
--   Actual Eisenstein Cubic: sextic Char zero iff mem
-- statement:
--   The Actual Eisenstein Cubic construction uses the sextic Char zero iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1393-L1399
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1393-L1399

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

theorem OAI.ActualEisensteinCubic.sexticChar_zero_iff_mem (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    sexticChar P hgood (Ideal.Quotient.mk P a) = 0 ↔ a ∈ P := by sorry
