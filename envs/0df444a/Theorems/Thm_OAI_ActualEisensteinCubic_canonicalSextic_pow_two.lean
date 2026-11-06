-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_two
-- name    : OAI.ActualEisensteinCubic.canonicalSextic_pow_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:10:30.99248+00:00
-- url     : https://prove2.me/theorems/983b23db-0b80-43b8-9f97-ebe1f7326123
-- title:
--   Actual Eisenstein Cubic: canonical Sextic pow two
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical Sextic pow two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L51-L56
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicNormalization.lean#L51-L56

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

theorem OAI.ActualEisensteinCubic.canonicalSextic_pow_two (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 2 =
      (cubicChar P hgood).ringHomComp eisEmbedding := by sorry
