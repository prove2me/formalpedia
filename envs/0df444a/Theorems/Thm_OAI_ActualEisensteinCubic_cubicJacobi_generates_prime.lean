-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_generates_prime
-- name    : OAI.ActualEisensteinCubic.cubicJacobi_generates_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:20:06.388168+00:00
-- url     : https://prove2.me/theorems/68114149-268c-4b8c-ba58-11c8ac734e75
-- title:
--   Actual Eisenstein Cubic: cubic Jacobi generates prime
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Jacobi generates prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1061-L1090
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1061-L1090

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

theorem OAI.ActualEisensteinCubic.cubicJacobi_generates_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    P = Ideal.span {jacobiSum (cubicChar P hgood) (cubicChar P hgood)} := by sorry
