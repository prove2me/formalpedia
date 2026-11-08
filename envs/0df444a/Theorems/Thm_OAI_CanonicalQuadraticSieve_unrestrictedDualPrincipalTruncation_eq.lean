-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_unrestrictedDualPrincipalTruncation_eq
-- name    : OAI.CanonicalQuadraticSieve.unrestrictedDualPrincipalTruncation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T16:13:40.472598+00:00
-- url     : https://prove2.me/theorems/80753e45-d1eb-4bb5-a9a0-99ca2164a829
-- title:
--   Canonical Quadratic Sieve: unrestricted Dual Principal Truncation eq
-- statement:
--   The Canonical Quadratic Sieve construction uses the unrestricted Dual Principal Truncation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/RetainedDualBounds.lean#L138-L178
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/RetainedDualBounds.lean#L138-L178

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
omit [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem OAI.CanonicalQuadraticSieve.unrestrictedDualPrincipalTruncation_eq
    (W : ℝ → ℂ) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k)) :
    unrestrictedDualPrincipalTruncation W rows left right a b M F Z =
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows left right a b (M/F) -
      paperRadialFourier W 0*unrestrictedLargePrincipalSum rows left right a b M F Z -
      W 0*unrestrictedSmallPrincipalSum rows left right a b M F (fun d i => (Ideal.absNorm d:ℝ) ≤ Z i) := by sorry
