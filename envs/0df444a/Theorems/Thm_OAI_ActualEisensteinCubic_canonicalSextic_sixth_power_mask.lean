-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_sixth_power_mask
-- name    : OAI.ActualEisensteinCubic.canonicalSextic_sixth_power_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:14:58.825229+00:00
-- url     : https://prove2.me/theorems/456ca3ed-f7d8-49c8-8f33-3ce221145967
-- title:
--   Actual Eisenstein Cubic: canonical Sextic sixth power mask
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical Sextic sixth power mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L542-L551
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L542-L551

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
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

theorem OAI.ActualEisensteinCubic.canonicalSextic_sixth_power_mask (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (a ^ 6)) =
      if a ∈ P then 0 else 1 := by sorry
