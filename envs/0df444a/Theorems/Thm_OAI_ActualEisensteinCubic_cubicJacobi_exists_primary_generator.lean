-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_exists_primary_generator
-- name    : OAI.ActualEisensteinCubic.cubicJacobi_exists_primary_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:00.229147+00:00
-- url     : https://prove2.me/theorems/8832659b-880d-484a-a59d-508b1537289d
-- title:
--   Actual Eisenstein Cubic: cubic Jacobi exists primary generator
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Jacobi exists primary generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1092-L1104
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1092-L1104

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

theorem OAI.ActualEisensteinCubic.cubicJacobi_exists_primary_generator (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 ∧
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by sorry
