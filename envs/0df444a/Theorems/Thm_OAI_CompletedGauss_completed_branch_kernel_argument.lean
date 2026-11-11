-- Prove2me | Theorems.Thm_OAI_CompletedGauss_completed_branch_kernel_argument
-- name    : OAI.CompletedGauss.completed_branch_kernel_argument
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:55:57.282196+00:00
-- url     : https://prove2.me/theorems/f5b55b1e-836a-4acb-a874-28735f110858
-- title:
--   Completed Gauss: completed branch kernel argument
-- statement:
--   The Completed Gauss construction uses the completed branch kernel argument property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/UnitNormalization.lean#L232-L253
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/UnitNormalization.lean#L232-L253

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_UnitNormalization
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
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CompletedDyadic

theorem OAI.CompletedGauss.completed_branch_kernel_argument {ι : Type*} [Fintype ι]
    (P : ι→Ideal ActualEisensteinCubic.O) (hP : ∀i,P i≠0) (e : ι→Fin 3)
    (K X c0 r U B : ℝ) (I F Q H N V : Ideal ActualEisensteinCubic.O)
    (hX : 0<X) (hc0 : 0<c0) (hK : 0<completedResidualScale K I Q)
    (hU : 0<U) (hB : 0<B) (hH : H≠0) (hN : N≠0) (hV : V≠0) :
    ((completedBranchScale K (X/c0^2) I F Q P e)⁻¹*r^3*B^3*U)*
      Real.exp (-2*Real.log ((Ideal.absNorm H:ℝ)/completedResidualScale K I Q)+
        Real.log ((Ideal.absNorm N:ℝ)/U)+3*Real.log ((Ideal.absNorm V:ℝ)/B)) =
      r^3*(Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1*N):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2*V):ℝ)^3*X/
        ((Ideal.absNorm H:ℝ)^2*(c0*(Ideal.absNorm (∏i,P i):ℝ))^2) := by sorry
