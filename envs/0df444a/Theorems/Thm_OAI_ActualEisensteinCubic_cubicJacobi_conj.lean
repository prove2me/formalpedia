-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_conj
-- name    : OAI.ActualEisensteinCubic.cubicJacobi_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:59.455398+00:00
-- url     : https://prove2.me/theorems/458a0fd4-c32d-4d05-b508-918905ac5e01
-- title:
--   Actual Eisenstein Cubic: cubic Jacobi conj
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Jacobi conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L767-L774
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L767-L774

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
open NumberField

theorem OAI.ActualEisensteinCubic.cubicJacobi_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ := by sorry
