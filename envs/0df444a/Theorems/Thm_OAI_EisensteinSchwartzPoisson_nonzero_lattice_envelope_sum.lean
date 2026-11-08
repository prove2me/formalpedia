-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_nonzero_lattice_envelope_sum
-- name    : OAI.EisensteinSchwartzPoisson.nonzero_lattice_envelope_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:52:22.787477+00:00
-- url     : https://prove2.me/theorems/2db012d7-42a6-4857-8323-8e4fcbedaead
-- title:
--   Eisenstein Schwartz Poisson: nonzero lattice envelope sum
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the nonzero lattice envelope sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/LatticeEnvelopes.lean#L104-L126
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/LatticeEnvelopes.lean#L104-L126

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstCoreCutoff
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_LatticeEnvelopes
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
open scoped BigOperators Classical SchwartzMap
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

theorem OAI.EisensteinSchwartzPoisson.nonzero_lattice_envelope_sum
    (t C : ℝ) (ht : 0 < t) (hC : 0 ≤ C)
    (f : {h : O // h ≠ 0} → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hbound : ∀ h, (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * f h ≤ C) :
    Summable f ∧ t * (∑' h, f h) ≤ nonzeroLatticeEnvelopeConstant * C := by sorry
