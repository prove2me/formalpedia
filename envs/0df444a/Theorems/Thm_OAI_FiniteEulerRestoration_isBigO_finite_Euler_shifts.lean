-- Prove2me | Theorems.Thm_OAI_FiniteEulerRestoration_isBigO_finite_Euler_shifts
-- name    : OAI.FiniteEulerRestoration.isBigO_finite_Euler_shifts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:10.967229+00:00
-- url     : https://prove2.me/theorems/03902645-6813-4ece-87fa-4e16857466b9
-- title:
--   Finite Euler Restoration: is Big O finite Euler shifts
-- statement:
--   The Finite Euler Restoration construction uses the is Big O finite Euler shifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L62-L75
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L62-L75

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

theorem OAI.FiniteEulerRestoration.isBigO_finite_Euler_shifts {ι : Type*} (s : Finset ι)
    (A : ℝ → ℂ) (c : ι → ℂ) (N : ι → ℝ) {σ : ℝ}
    (hN : ∀ i ∈ s, 0 < N i)
    (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => ∑ i ∈ s, c i * A (D / N i)) =O[atTop]
      (fun D : ℝ => D ^ σ) := by sorry
