-- Prove2me | Theorems.Thm_OAI_QuadraticUnitInvariance_quadratic_pair_lattice_eq_primary_ideal_sum
-- name    : OAI.QuadraticUnitInvariance.quadratic_pair_lattice_eq_primary_ideal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:13:14.697921+00:00
-- url     : https://prove2.me/theorems/739c56f4-5ae7-43fa-b433-6d3a90ef6cc8
-- title:
--   Quadratic Unit Invariance: quadratic pair lattice eq primary ideal sum
-- statement:
--   The Quadratic Unit Invariance construction uses the quadratic pair lattice eq primary ideal sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean#L469-L505
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean#L469-L505

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss

theorem OAI.QuadraticUnitInvariance.quadratic_pair_lattice_eq_primary_ideal_sum
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i))
    (R : α → Ideal O) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (primaryGenerator I.val)) *
      W ((Ideal.absNorm I.val : ℝ) / M) := by sorry
