-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_unit_multiple
-- name    : OAI.ActualEisensteinCubic.cubicJacobi_unit_multiple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:20:06.857328+00:00
-- url     : https://prove2.me/theorems/5041d30d-7cf4-4d51-bd6e-95536237148c
-- title:
--   Actual Eisenstein Cubic: cubic Jacobi unit multiple
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Jacobi unit multiple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L829-L850
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L829-L850

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

theorem OAI.ActualEisensteinCubic.cubicJacobi_unit_multiple (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hnorm : p * conjO p = (Nat.card (O ⧸ P) : O)) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by sorry
