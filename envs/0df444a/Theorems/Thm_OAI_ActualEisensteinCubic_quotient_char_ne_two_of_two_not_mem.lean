-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_quotient_char_ne_two_of_two_not_mem
-- name    : OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:22.114718+00:00
-- url     : https://prove2.me/theorems/f5a248cf-7479-49a4-96da-7023060f939b
-- title:
--   Actual Eisenstein Cubic: quotient char ne two of two not mem
-- statement:
--   The Actual Eisenstein Cubic construction uses the quotient char ne two of two not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1384-L1391
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1384-L1391

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

theorem OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by sorry
