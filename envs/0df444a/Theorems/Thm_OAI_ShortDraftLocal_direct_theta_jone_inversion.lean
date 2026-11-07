-- Prove2me | Theorems.Thm_OAI_ShortDraftLocal_direct_theta_jone_inversion
-- name    : OAI.ShortDraftLocal.direct_theta_jone_inversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:43:50.831785+00:00
-- url     : https://prove2.me/theorems/b78a51a6-d83d-46d5-b92a-45ebd1ade231
-- title:
--   Short Draft Local: direct theta jone inversion
-- statement:
--   The Short Draft Local construction uses the direct theta jone inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L509-L527
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L509-L527

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

theorem OAI.ShortDraftLocal.direct_theta_jone_inversion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum χ⁻¹ (ψ.mulShift a) := by sorry
