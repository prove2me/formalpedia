-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_SubexponentialBesselCoefficients_fullFunction_translate_split_contDiffAt_one
-- name    : OAI.CubicEisenstein.SubexponentialBesselCoefficients.fullFunction_translate_split_contDiffAt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:15:45.001438+00:00
-- url     : https://prove2.me/theorems/f4939988-64ff-48d1-9ce5-3c682ceb5e86
-- title:
--   Subexponential Bessel Coefficients: full Function translate split cont Diff At one
-- statement:
--   The Subexponential Bessel Coefficients construction uses the full Function translate split cont Diff At one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ConjugateCuspProfiles.lean#L316-L320
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ConjugateCuspProfiles.lean#L316-L320

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ArbitraryCuspPullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubeCorrespondence
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateCuspProfiles
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
open Finset AddChar MulChar EisensteinEmbedding
open OAI.CubicEisenstein.SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

theorem OAI.CubicEisenstein.SubexponentialBesselCoefficients.fullFunction_translate_split_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>coeff.fullFunction constant (g•cuspCoordinateLift (q.2,q.1))) p := by sorry
