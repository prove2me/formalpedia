-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_quadraticGammaO_rational
-- name    : OAI.ActualEisensteinCubic.quadraticGammaO_rational
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:25:00.330729+00:00
-- url     : https://prove2.me/theorems/293e1c35-5e73-4b90-bf75-425fe50e8f58
-- title:
--   Actual Eisenstein Cubic: quadratic Gamma O rational
-- statement:
--   The Actual Eisenstein Cubic construction uses the quadratic Gamma O rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L37-L39
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L37-L39

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

theorem OAI.ActualEisensteinCubic.quadraticGammaO_rational (m : ℕ) (hm : m ≠ 0)
    (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = quadraticGammaRational m hm := by sorry
