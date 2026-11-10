-- Prove2me | Theorems.Thm_OAI_QRH_b83dbbd_CanonicalQuadraticSieve_HasSieveExponent_lifted_annular_selected
-- name    : OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.lifted_annular_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T06:22:47.732104+00:00
-- url     : https://prove2.me/theorems/336da1aa-aa65-4124-a8ac-f71ce1bd9f69
-- title:
--   Has Sieve Exponent: lifted annular selected
-- statement:
--   The Has Sieve Exponent construction uses the lifted annular selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/LogarithmicLoss.lean#L83-L138
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/LogarithmicLoss.lean#L83-L138

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
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
open OAI.CanonicalQuadraticSieve

theorem OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.lifted_annular_selected {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1≤q → q≤7 →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ)^j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by sorry

alias «OAI».«CanonicalQuadraticSieve».«HasSieveExponent».«lifted_annular_selected» := OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.lifted_annular_selected
