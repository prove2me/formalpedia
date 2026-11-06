-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_principal_absNorm_pow
-- name    : OAI.ActualEisensteinCubic.principal_absNorm_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:45:22.323314+00:00
-- url     : https://prove2.me/theorems/f5fd20b7-eaf8-47d8-a147-3a3eb72f35cc
-- title:
--   Actual Eisenstein Cubic: principal abs Norm pow
-- statement:
--   The Actual Eisenstein Cubic construction uses the principal abs Norm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L20-L24
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L20-L24

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
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

theorem OAI.ActualEisensteinCubic.principal_absNorm_pow (p : O) (k : ℕ) :
    Ideal.absNorm (Ideal.span {p ^ k}) =
      (Ideal.absNorm (Ideal.span {p})) ^ k := by sorry
