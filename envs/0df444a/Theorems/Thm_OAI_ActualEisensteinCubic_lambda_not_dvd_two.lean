-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_lambda_not_dvd_two
-- name    : OAI.ActualEisensteinCubic.lambda_not_dvd_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:29.950654+00:00
-- url     : https://prove2.me/theorems/5db540be-ff04-481d-b19a-2ce5fb28f3e9
-- title:
--   Actual Eisenstein Cubic: lambda not dvd two
-- statement:
--   The Actual Eisenstein Cubic construction uses the lambda not dvd two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L852-L880
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L852-L880

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

theorem OAI.ActualEisensteinCubic.lambda_not_dvd_two : ¬ lambda ∣ (2 : O) := by sorry
