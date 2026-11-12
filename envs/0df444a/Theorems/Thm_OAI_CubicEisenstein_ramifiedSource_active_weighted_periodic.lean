-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_active_weighted_periodic
-- name    : OAI.CubicEisenstein.ramifiedSource_active_weighted_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:27:41.397198+00:00
-- url     : https://prove2.me/theorems/407ed97d-2b9d-4b66-a536-5bec648e0ad6
-- title:
--   Cubic Eisenstein: ramified Source active weighted periodic
-- statement:
--   The Cubic Eisenstein construction uses the ramified Source active weighted periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedSixBranches.lean#L537-L549
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedSixBranches.lean#L537-L549

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedSixBranches
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
open scoped BigOperators Classical Topology MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem OAI.CubicEisenstein.ramifiedSource_active_weighted_periodic (b : Bool) (h : Eis)
    (hh : (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    ∀x : Eis,∀z : ℂ,
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by sorry
