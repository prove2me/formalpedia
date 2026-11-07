-- Prove2me | Theorems.Thm_OAI_ShortDraftLocal_direct_theta_jone_not_quadratic
-- name    : OAI.ShortDraftLocal.direct_theta_jone_not_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:44:04.153491+00:00
-- url     : https://prove2.me/theorems/9ca2b32e-eb37-4025-871d-19bab91d966c
-- title:
--   Short Draft Local: direct theta jone not quadratic
-- statement:
--   The Short Draft Local construction uses the direct theta jone not quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L576-L583
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L576-L583

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open OAI.ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F] [DecidableEq F]

theorem OAI.ShortDraftLocal.direct_theta_jone_not_quadratic (χ : MulChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) : χ ≠ χ ^ 3 := by sorry
