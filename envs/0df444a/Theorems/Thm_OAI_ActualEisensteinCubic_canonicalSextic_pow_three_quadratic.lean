-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_three_quadratic
-- name    : OAI.ActualEisensteinCubic.canonicalSextic_pow_three_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:20.960173+00:00
-- url     : https://prove2.me/theorems/364b6fb9-117a-4808-826f-2d059a09fd3a
-- title:
--   Actual Eisenstein Cubic: canonical Sextic pow three quadratic
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical Sextic pow three quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L40-L49
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticNormalization.lean#L40-L49

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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

theorem OAI.ActualEisensteinCubic.canonicalSextic_pow_three_quadratic (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 3 =
      (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ) := by sorry
