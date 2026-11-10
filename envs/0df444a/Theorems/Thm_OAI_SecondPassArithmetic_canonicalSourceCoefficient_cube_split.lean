-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceCoefficient_cube_split
-- name    : OAI.SecondPassArithmetic.canonicalSourceCoefficient_cube_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:23:57.955381+00:00
-- url     : https://prove2.me/theorems/ef7aebf8-e801-4ae0-a160-4eb50f531596
-- title:
--   Second Pass Arithmetic: canonical Source Coefficient cube split
-- statement:
--   The Second Pass Arithmetic construction uses the canonical Source Coefficient cube split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L375-L404
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L375-L404

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_OutsideIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem OAI.SecondPassArithmetic.canonicalSourceCoefficient_cube_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (B C S : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (hCB : Disjoint C B) (hSC : Disjoint S C) (hSB : Disjoint S B) :
    let A := B.filter (fun i => if negative then ε₂ i else ε₁ i)
    canonicalSourceCoefficient p hp hcop hg Ψ m f H ((A∪C)∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) (A∪C) *
      (columnCoefficient p hp hcop hg S *
        originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => H ((A∪C)∪U)))
          (∏i∈C,p i) f S) := by sorry
