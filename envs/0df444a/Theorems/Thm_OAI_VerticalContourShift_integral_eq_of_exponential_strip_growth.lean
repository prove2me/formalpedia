-- Prove2me | Theorems.Thm_OAI_VerticalContourShift_integral_eq_of_exponential_strip_growth
-- name    : OAI.VerticalContourShift.integral_eq_of_exponential_strip_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:48:40.040401+00:00
-- url     : https://prove2.me/theorems/06565c9e-6992-4f8b-944e-267ac708e43f
-- title:
--   Vertical Contour Shift: integral eq of exponential strip growth
-- statement:
--   The Vertical Contour Shift construction uses the integral eq of exponential strip growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean#L248-L283
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean#L248-L283

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_VerticalContourShift
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
open OAI.VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

theorem OAI.VerticalContourShift.integral_eq_of_exponential_strip_growth
    (f : ℂ→ℂ) (a b A B : ℝ) (hab : a≤b) (hA : 0≤A) (hB : 0≤B)
    (hdiff : ∀z : ℂ,a≤z.re→z.re≤b→DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)))
    (hb : Integrable (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)))
    (hbound : ∀σ∈Set.Icc a b,∀t : ℝ,‖f ((σ:ℂ)+t*Complex.I)‖≤B*Real.exp (A*|t|)) :
    (∫t : ℝ,f ((a:ℂ)+t*Complex.I))=∫t : ℝ,f ((b:ℂ)+t*Complex.I) := by sorry
