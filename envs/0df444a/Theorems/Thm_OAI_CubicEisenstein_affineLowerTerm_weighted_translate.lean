-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_affineLowerTerm_weighted_translate
-- name    : OAI.CubicEisenstein.affineLowerTerm_weighted_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:04:09.490313+00:00
-- url     : https://prove2.me/theorems/beed092a-94df-41eb-8be3-74ba17659cb0
-- title:
--   Cubic Eisenstein: affine Lower Term weighted translate
-- statement:
--   The Cubic Eisenstein construction uses the affine Lower Term weighted translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean#L145-L192
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean#L145-L192

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
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
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

theorem OAI.CubicEisenstein.affineLowerTerm_weighted_translate (h h1 q r a k x m:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a (a+3*(x+a*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affineLowerTerm q r (z+3*eisEmbedding m/eisEmbedding q) v s a (a+3*x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q)) := by sorry
