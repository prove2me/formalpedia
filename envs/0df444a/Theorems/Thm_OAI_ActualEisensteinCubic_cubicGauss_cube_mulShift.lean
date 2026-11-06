-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_cube_mulShift
-- name    : OAI.ActualEisensteinCubic.cubicGauss_cube_mulShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:35:10.304545+00:00
-- url     : https://prove2.me/theorems/064177a4-6c35-4ae4-befd-d1830c0adc9e
-- title:
--   Actual Eisenstein Cubic: cubic Gauss cube mul Shift
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Gauss cube mul Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1261-L1276
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L1261-L1276

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

theorem OAI.ActualEisensteinCubic.cubicGauss_cube_mulShift {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (ψ : AddChar (O ⧸ P) E) (a : (O ⧸ P)ˣ) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) (ψ.mulShift a) ^ 3 =
      gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 := by sorry
