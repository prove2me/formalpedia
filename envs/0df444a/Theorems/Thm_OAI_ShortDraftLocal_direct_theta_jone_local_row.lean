-- Prove2me | Theorems.Thm_OAI_ShortDraftLocal_direct_theta_jone_local_row
-- name    : OAI.ShortDraftLocal.direct_theta_jone_local_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:44:08.073964+00:00
-- url     : https://prove2.me/theorems/61fc5ce4-d76f-4295-ae02-69f2a61fb53d
-- title:
--   Short Draft Local: direct theta jone local row
-- statement:
--   The Short Draft Local construction uses the direct theta jone local row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L529-L563
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L529-L563

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

theorem OAI.ShortDraftLocal.direct_theta_jone_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) * χ x := by sorry
