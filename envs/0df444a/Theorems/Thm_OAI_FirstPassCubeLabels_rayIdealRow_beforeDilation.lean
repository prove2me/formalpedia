-- Prove2me | Theorems.Thm_OAI_FirstPassCubeLabels_rayIdealRow_beforeDilation
-- name    : OAI.FirstPassCubeLabels.rayIdealRow_beforeDilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:39:21.505918+00:00
-- url     : https://prove2.me/theorems/a7d0d1b8-f342-412c-aaef-9a5dc3aad453
-- title:
--   First Pass Cube Labels: ray Ideal Row before Dilation
-- statement:
--   The First Pass Cube Labels construction uses the ray Ideal Row before Dilation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/KernelEnergy.lean#L277-L308
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/KernelEnergy.lean#L277-L308

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
set_option autoImplicit false
open OAI
noncomputable section
open OAI.FirstPassCubeLabels
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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

theorem OAI.FirstPassCubeLabels.rayIdealRow_beforeDilation {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (c d f h : O) :
    rayIdealRow p hg F
      (fun S => C S * beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f S)
      negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      dilatedRayColumn p hg F D C negative χ q B v ε₁ ε₂ c d
        (h * f ^ 2 * dilationLabel q B v ε₁ ε₂) := by sorry
