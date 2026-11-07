-- Prove2me | Theorems.Thm_OAI_DyadicTransfer_finite_exp_reassembly
-- name    : OAI.DyadicTransfer.finite_exp_reassembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:59.318104+00:00
-- url     : https://prove2.me/theorems/1d0d9ec3-53e8-48da-9bab-c5681a8a4802
-- title:
--   Dyadic Transfer: finite exp reassembly
-- statement:
--   The Dyadic Transfer construction uses the finite exp reassembly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L470-L498
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L470-L498

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
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
open OAI.DyadicTransfer

theorem OAI.DyadicTransfer.finite_exp_reassembly (a : ℕ → ℂ) (φ : ℝ → ℂ)
    (ha0 : a 0 = 0)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (D : ℝ) (N K : ℕ)
    (hK : ∀ n ∈ Finset.range N, 1 ≤ n → (n : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) / D)) =
      ∑ k ∈ Finset.range (K + 1),
        ∑ n ∈ Finset.range N,
          a n * expAnnularTest φ D k ((n : ℝ) / (2 : ℝ) ^ k) := by sorry
