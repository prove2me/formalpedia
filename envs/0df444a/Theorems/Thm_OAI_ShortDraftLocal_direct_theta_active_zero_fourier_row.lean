-- Prove2me | Theorems.Thm_OAI_ShortDraftLocal_direct_theta_active_zero_fourier_row
-- name    : OAI.ShortDraftLocal.direct_theta_active_zero_fourier_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:45:46.037201+00:00
-- url     : https://prove2.me/theorems/196fa808-9d9f-4211-a86e-fd1ae15a5386
-- title:
--   Short Draft Local: direct theta active zero fourier row
-- statement:
--   The Short Draft Local construction uses the direct theta active zero fourier row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L528-L557
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L528-L557

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

theorem OAI.ShortDraftLocal.direct_theta_active_zero_fourier_row (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hχ₂ : χ ^ 2 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (-(Fintype.card F : ℂ)⁻¹) *
      (∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by sorry
