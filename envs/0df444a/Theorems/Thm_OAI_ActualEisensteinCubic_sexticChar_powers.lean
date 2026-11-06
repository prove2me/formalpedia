-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_powers
-- name    : OAI.ActualEisensteinCubic.sexticChar_powers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:58.429295+00:00
-- url     : https://prove2.me/theorems/2635c3bb-5a30-449c-9375-621a2ce7032b
-- title:
--   Actual Eisenstein Cubic: sextic Char powers
-- statement:
--   The Actual Eisenstein Cubic construction uses the sextic Char powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L805-L827
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L805-L827

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

theorem OAI.ActualEisensteinCubic.sexticChar_powers (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    sexticChar P hgood ^ 2 = cubicChar P hgood ∧
    sexticChar P hgood ^ 3 = quadraticCharO P ∧
    sexticChar P hgood ^ 6 = 1 := by sorry
