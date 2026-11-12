-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_affineCusp_branch_fourier
-- name    : OAI.CubicEisenstein.affineCusp_branch_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:48:23.639425+00:00
-- url     : https://prove2.me/theorems/80bf0966-ffae-4ebe-ac10-6e292de83057
-- title:
--   Cubic Eisenstein: affine Cusp branch fourier
-- statement:
--   The Cubic Eisenstein construction uses the affine Cusp branch fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean#L272-L307
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean#L272-L307

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

theorem OAI.CubicEisenstein.affineCusp_branch_fourier (h h1 q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
            unramifiedCubicGaussSeries s (3*r^2*h1) := by sorry
