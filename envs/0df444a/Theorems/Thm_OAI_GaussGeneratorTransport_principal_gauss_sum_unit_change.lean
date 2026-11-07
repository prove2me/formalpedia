-- Prove2me | Theorems.Thm_OAI_GaussGeneratorTransport_principal_gauss_sum_unit_change
-- name    : OAI.GaussGeneratorTransport.principal_gauss_sum_unit_change
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:10:55.683207+00:00
-- url     : https://prove2.me/theorems/866e3f0d-4f29-4099-ab30-89fad655ed60
-- title:
--   Gauss Generator Transport: principal gauss sum unit change
-- statement:
--   The Gauss Generator Transport construction uses the principal gauss sum unit change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicTrace.lean#L364-L398
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicTrace.lean#L364-L398

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
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
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem OAI.GaussGeneratorTransport.principal_gauss_sum_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n)
    [Fintype (O ⧸ Ideal.span {c})] [Fintype (O ⧸ Ideal.span {n})] :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) =
      finiteSexticRow P hgood j (u : O) *
        ∑ r : O ⧸ Ideal.span {n}, principalSexticRow P hcop hgood j n hn r *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0 r := by sorry
