-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_order
-- name    : OAI.ActualEisensteinCubic.sexticChar_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:20:21.968533+00:00
-- url     : https://prove2.me/theorems/e4dcb004-1bd5-4b98-a8a2-ce6951ff9a13
-- title:
--   Actual Eisenstein Cubic: sextic Char order
-- statement:
--   The Actual Eisenstein Cubic construction uses the sextic Char order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1287-L1321
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1287-L1321

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

theorem OAI.ActualEisensteinCubic.sexticChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (sexticChar P hgood) = 6 := by sorry
