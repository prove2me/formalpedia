-- Prove2me | Theorems.Thm_OAI_CompletedGauss_cusp_summand_eq_local_branches
-- name    : OAI.CompletedGauss.cusp_summand_eq_local_branches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:23:38.732648+00:00
-- url     : https://prove2.me/theorems/d521e52b-ded8-4e83-83d4-6dd06d22c56f
-- title:
--   Completed Gauss: cusp summand eq local branches
-- statement:
--   The Completed Gauss construction uses the cusp summand eq local branches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RowCompletion/CompletedEnergy.lean#L255-L274
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RowCompletion/CompletedEnergy.lean#L255-L274

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_UnitNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CompletedEnergy
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CompletedDyadic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.CompletedGauss.cusp_summand_eq_local_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (j : ι→ℕ)
    (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ) (ζ : ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) (hn : n≠0) (hb : b≠0) :
    (ζ*(d (fractionalThetaPoint u m n b)/(‖fractionalThetaPoint u m n b‖:ℂ)))*
      (fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ))*
      vartheta (u.val*lambda^m*(n*b^3))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (u.val*lambda^m*(n*b^3)))) =
    (4/3:ℂ)*(81*ζ)*ramifiedBranchPhase P hg j u m*
      ∑e : ι→Fin 3,
        (normalizedThetaAmplitude d vartheta u m n b*reflectedBranch P hg j e n b)/
          ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*
            ‖eisEmbedding n‖*‖eisEmbedding b‖^2:ℝ):ℂ) := by sorry
