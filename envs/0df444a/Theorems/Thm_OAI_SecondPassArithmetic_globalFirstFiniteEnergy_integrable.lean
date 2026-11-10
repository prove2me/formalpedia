-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalFirstFiniteEnergy_integrable
-- name    : OAI.SecondPassArithmetic.globalFirstFiniteEnergy_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T07:52:49.28047+00:00
-- url     : https://prove2.me/theorems/feda31b4-2086-48a8-b2d8-20d1a055e5bc
-- title:
--   Second Pass Arithmetic: global First Finite Energy integrable
-- statement:
--   The Second Pass Arithmetic construction uses the global First Finite Energy integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/TransformedColumns.lean#L386-L404
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/TransformedColumns.lean#L386-L404

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem OAI.SecondPassArithmetic.globalFirstFiniteEnergy_integrable (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    Integrable (fun t => firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t) := by sorry
