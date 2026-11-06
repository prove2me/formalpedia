-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_breveGamma2_cube
-- name    : OAI.ActualEisensteinCubic.breveGamma2_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:30.329465+00:00
-- url     : https://prove2.me/theorems/bcd0dc76-7a73-451c-bc6f-c4be6004ccf1
-- title:
--   Actual Eisenstein Cubic: breve Gamma2 cube
-- statement:
--   The Actual Eisenstein Cubic construction uses the breve Gamma2 cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L58-L65
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L58-L65

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
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
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT

theorem OAI.ActualEisensteinCubic.breveGamma2_cube (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (breveGamma2 P hgood p hP hp) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by sorry
