-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_eq_neg_primary_generator_trace
-- name    : OAI.ActualEisensteinCubic.cubicJacobi_eq_neg_primary_generator_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:08.077032+00:00
-- url     : https://prove2.me/theorems/4e597c71-e701-4385-bcf4-54daa020697c
-- title:
--   Actual Eisenstein Cubic: cubic Jacobi eq neg primary generator trace
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Jacobi eq neg primary generator trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1111-L1118
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1111-L1118

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

theorem OAI.ActualEisensteinCubic.cubicJacobi_eq_neg_primary_generator_trace (P : Ideal O) [P.IsMaximal]
    (hgood : traceLambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : traceLambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P (hgood_from_trace P hgood))
      (cubicChar P (hgood_from_trace P hgood)) = -p := by sorry
