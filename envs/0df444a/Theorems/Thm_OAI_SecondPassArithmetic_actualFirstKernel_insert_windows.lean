-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_actualFirstKernel_insert_windows
-- name    : OAI.SecondPassArithmetic.actualFirstKernel_insert_windows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:55:56.17583+00:00
-- url     : https://prove2.me/theorems/497d7a50-fa24-43cd-a25e-6017600cbc96
-- title:
--   Second Pass Arithmetic: actual First Kernel insert windows
-- statement:
--   The Second Pass Arithmetic construction uses the actual First Kernel insert windows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean#L120-L148
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean#L120-L148

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem OAI.SecondPassArithmetic.actualFirstKernel_insert_windows
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (Ψ₁ Ψ₂:O→*ℂ)
    (m₁ m₂ c f:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (X₁ X₂ K:ℝ) (d h:O)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W (fun _=>1) (fun _=>1) X₁ X₂ K d h =
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W V₁ V₂ X₁ X₂ K d h := by sorry
