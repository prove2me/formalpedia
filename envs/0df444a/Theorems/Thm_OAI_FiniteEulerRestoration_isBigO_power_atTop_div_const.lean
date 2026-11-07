-- Prove2me | Theorems.Thm_OAI_FiniteEulerRestoration_isBigO_power_atTop_div_const
-- name    : OAI.FiniteEulerRestoration.isBigO_power_atTop_div_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:45.664855+00:00
-- url     : https://prove2.me/theorems/3a1c823c-9647-40ae-bcb8-414098088da4
-- title:
--   Finite Euler Restoration: is Big O power at Top div const
-- statement:
--   The Finite Euler Restoration construction uses the is Big O power at Top div const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L45-L60
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L45-L60

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

theorem OAI.FiniteEulerRestoration.isBigO_power_atTop_div_const {A : ℝ → ℂ} {σ N : ℝ}
    (hN : 0 < N) (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => A (D / N)) =O[atTop] (fun D : ℝ => D ^ σ) := by sorry
