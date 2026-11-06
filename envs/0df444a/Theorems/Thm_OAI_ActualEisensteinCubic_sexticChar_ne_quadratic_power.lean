-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_ne_quadratic_power
-- name    : OAI.ActualEisensteinCubic.sexticChar_ne_quadratic_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:19.22776+00:00
-- url     : https://prove2.me/theorems/a1acadcc-7021-42a3-a6f1-10e8443f3b56
-- title:
--   Actual Eisenstein Cubic: sextic Char ne quadratic power
-- statement:
--   The Actual Eisenstein Cubic construction uses the sextic Char ne quadratic power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1323-L1335
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1323-L1335

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

theorem OAI.ActualEisensteinCubic.sexticChar_ne_quadratic_power (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    sexticChar P hgood ≠ (sexticChar P hgood) ^ 3 := by sorry
