-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_integralCoverTraceFunction_cusp_decay
-- name    : OAI.CubicEisenstein.integralCoverTraceFunction_cusp_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:16:37.275106+00:00
-- url     : https://prove2.me/theorems/9ad1a56c-9831-415e-a0af-0f52b6b51666
-- title:
--   Cubic Eisenstein: integral Cover Trace Function cusp decay
-- statement:
--   The Cubic Eisenstein construction uses the integral Cover Trace Function cusp decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CoverTrace.lean#L334-L373
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CoverTrace.lean#L334-L373

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace InnerProduct
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O

theorem OAI.CubicEisenstein.integralCoverTraceFunction_cusp_decay (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (complexMatrix M•upperPoint z v hv))‖≤C/v^3)
    (M : CubicKubota.levelThree) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖integralCoverTraceFunction H K f
      (integralOrbitProjection K (complexMatrix M•upperPoint z v hv))‖≤
        (H.relIndex K:ℝ)*C/v^3 := by sorry
