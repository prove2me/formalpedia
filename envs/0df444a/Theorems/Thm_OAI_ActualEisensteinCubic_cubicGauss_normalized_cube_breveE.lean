-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_normalized_cube_breveE
-- name    : OAI.ActualEisensteinCubic.cubicGauss_normalized_cube_breveE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:23.629036+00:00
-- url     : https://prove2.me/theorems/b60fbbf3-625c-4a7f-8250-9fa8a79f5f80
-- title:
--   Actual Eisenstein Cubic: cubic Gauss normalized cube breve E
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Gauss normalized cube breve E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L24-L37
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L24-L37

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
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

theorem OAI.ActualEisensteinCubic.cubicGauss_normalized_cube_breveE
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp eisEmbedding)
      (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by sorry
