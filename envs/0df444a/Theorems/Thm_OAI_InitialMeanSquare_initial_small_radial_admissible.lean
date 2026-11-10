-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_small_radial_admissible
-- name    : OAI.InitialMeanSquare.initial_small_radial_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:21:32.396193+00:00
-- url     : https://prove2.me/theorems/38e3706e-02f0-4169-940e-5eb23914cb99
-- title:
--   Initial Mean Square: initial small radial admissible
-- statement:
--   The Initial Mean Square construction uses the initial small radial admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ReflectedBranches.lean#L332-L358
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ReflectedBranches.lean#L332-L358

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_NormalizedMass
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
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
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open SecondPassArithmetic

theorem OAI.InitialMeanSquare.initial_small_radial_admissible (Z B R c σ θ deltaLoss : ℝ) (j : SecondLogIndex)
    (hZ : 1≤Z) (hB : 0<B) (hR : R≤c*B) (hc : 0≤c) (hcZ : c≤Z^deltaLoss)
    (hmargin : deltaLoss+θ≤σ-(1:ℝ)/40)
    (hrad : Z^(1+σ)*secondLogK j*B^2/Z^2≤Z^θ) :
    (secondLogK j*Real.exp 2)*R≤
      initialLogColumn Z B j*initialLogLabel j*Z^(-(1:ℝ)/40) := by sorry
