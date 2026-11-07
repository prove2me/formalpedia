-- Prove2me | Theorems.Thm_OAI_ShortDraftLocal_direct_theta_jtwo_mask
-- name    : OAI.ShortDraftLocal.direct_theta_jtwo_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:45:44.055356+00:00
-- url     : https://prove2.me/theorems/d82588f9-29d7-4dc0-af9b-94df06fdd8dc
-- title:
--   Short Draft Local: direct theta jtwo mask
-- statement:
--   The Short Draft Local construction uses the direct theta jtwo mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L460-L475
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L460-L475

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
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
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open OAI.ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem OAI.ShortDraftLocal.direct_theta_jtwo_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2 * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by sorry
