-- Prove2me | Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_identity_gt_two
-- name    : OAI.CompactMellinBridge.pair_zero_free_of_identity_gt_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:28.324045+00:00
-- url     : https://prove2.me/theorems/3943c680-3107-4a90-88ef-5c20d5a11ecb
-- title:
--   Compact Mellin Bridge: pair zero free of identity gt two
-- statement:
--   The Compact Mellin Bridge construction uses the pair zero free of identity gt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L613-L714
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L613-L714

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.CompactMellinBridge

theorem OAI.CompactMellinBridge.pair_zero_free_of_identity_gt_two
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hnotboth : χ ≠ 1 ∨ ψ ≠ 1)
    (σ : ℝ) (hσ : σ < 1) (M W : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | σ < s.re})
    (heq : ∀ s : ℂ, 2 < s.re →
      (χ.LFunction s * ψ.LFunction s) * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by sorry
