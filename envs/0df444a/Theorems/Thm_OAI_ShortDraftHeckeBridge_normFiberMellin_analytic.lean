-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberMellin_analytic
-- name    : OAI.ShortDraftHeckeBridge.normFiberMellin_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:59.000747+00:00
-- url     : https://prove2.me/theorems/55bc8351-33c1-4dad-a2aa-5011c2f368b6
-- title:
--   Short Draft Hecke Bridge: norm Fiber Mellin analytic
-- statement:
--   The Short Draft Hecke Bridge construction uses the norm Fiber Mellin analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L565-L592
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L565-L592

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
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
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.normFiberMellin_analytic
    (weight : Ideal O → ℂ) (σ : ℝ) (hσpos : 0 < σ)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b)) :
    AnalyticOnNhd ℂ (normFiberMellin weight) {s : ℂ | σ < s.re} := by sorry
