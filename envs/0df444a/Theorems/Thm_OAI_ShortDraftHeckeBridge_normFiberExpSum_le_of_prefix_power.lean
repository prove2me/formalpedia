-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_le_of_prefix_power
-- name    : OAI.ShortDraftHeckeBridge.normFiberExpSum_le_of_prefix_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:13:46.348385+00:00
-- url     : https://prove2.me/theorems/5b9a7d8e-9396-45ad-bb6c-dfc7fa94a2c6
-- title:
--   Short Draft Hecke Bridge: norm Fiber Exp Sum le of prefix power
-- statement:
--   The Short Draft Hecke Bridge construction uses the norm Fiber Exp Sum le of prefix power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L663-L733
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L663-L733

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
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
open Filter Asymptotics
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.normFiberExpSum_le_of_prefix_power
    {q r₀ : ℕ} [NeZero q] [NeZero r₀]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r₀)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ C : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖prefixCoeff (normFiberCoeff weight) n‖ ≤ C * (((n : ℝ) + 1) ^ σ))
    (D : ℝ) (hD : 1 ≤ D) :
    ‖normFiberExpSum weight D⁻¹‖ ≤ 3 * C * D ^ σ := by sorry
