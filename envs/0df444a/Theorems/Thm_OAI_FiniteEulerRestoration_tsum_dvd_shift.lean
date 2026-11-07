-- Prove2me | Theorems.Thm_OAI_FiniteEulerRestoration_tsum_dvd_shift
-- name    : OAI.FiniteEulerRestoration.tsum_dvd_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:34.637203+00:00
-- url     : https://prove2.me/theorems/c4889ca9-2491-47ef-83c4-e1073100e449
-- title:
--   Finite Euler Restoration: tsum dvd shift
-- statement:
--   The Finite Euler Restoration construction uses the tsum dvd shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L77-L105
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L77-L105

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
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
open OAI.FiniteEulerRestoration

theorem OAI.FiniteEulerRestoration.tsum_dvd_shift {N : ℕ} (hN : 0 < N)
    (b : ℕ → ℂ) (φ : ℕ → ℂ) :
    (∑' n : ℕ, if N ∣ n then b (n / N) * φ n else 0) =
      ∑' m : ℕ, b m * φ (N * m) := by sorry
