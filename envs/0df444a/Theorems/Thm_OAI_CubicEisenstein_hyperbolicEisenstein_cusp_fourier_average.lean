-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_hyperbolicEisenstein_cusp_fourier_average
-- name    : OAI.CubicEisenstein.hyperbolicEisenstein_cusp_fourier_average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:58:54.066504+00:00
-- url     : https://prove2.me/theorems/214fe636-137b-4afd-834a-8f473e80ad3f
-- title:
--   Cubic Eisenstein: hyperbolic Eisenstein cusp fourier average
-- statement:
--   The Cubic Eisenstein construction uses the hyperbolic Eisenstein cusp fourier average property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringCoefficients.lean#L550-L569
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringCoefficients.lean#L550-L569

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CutoffApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateLevelAction
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ScatteringCoefficients
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
local notation "O" => ActualEisensteinCubic.O

theorem OAI.CubicEisenstein.hyperbolicEisenstein_cusp_fourier_average (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((if h=0 then (v:ℂ)^s else 0)+
          (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by sorry
