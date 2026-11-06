-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_norm_int_eq_mul_conjO
-- name    : OAI.ActualEisensteinCubic.norm_int_eq_mul_conjO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:20.663395+00:00
-- url     : https://prove2.me/theorems/f507c30b-8af2-4843-ab87-4e89db5d8620
-- title:
--   Actual Eisenstein Cubic: norm int eq mul conj O
-- statement:
--   The Actual Eisenstein Cubic construction uses the norm int eq mul conj O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L955-L961
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L955-L961

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

theorem OAI.ActualEisensteinCubic.norm_int_eq_mul_conjO (p : O) :
    ((Algebra.norm ℤ p : ℤ) : O) = p * conjO p := by sorry
