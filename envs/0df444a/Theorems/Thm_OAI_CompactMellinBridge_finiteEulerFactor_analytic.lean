-- Prove2me | Theorems.Thm_OAI_CompactMellinBridge_finiteEulerFactor_analytic
-- name    : OAI.CompactMellinBridge.finiteEulerFactor_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:21.679119+00:00
-- url     : https://prove2.me/theorems/2875386f-3f1b-47e5-93a3-95ee18de3a27
-- title:
--   Compact Mellin Bridge: finite Euler Factor analytic
-- statement:
--   The Compact Mellin Bridge construction uses the finite Euler Factor analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L445-L464
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L445-L464

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
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
open OAI.CompactMellinBridge

theorem OAI.CompactMellinBridge.finiteEulerFactor_analytic
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ShortDraftHeckeBridge.O))
    (hprime : ∀ P ∈ S, Prime P) (σ : ℝ) :
    AnalyticOnNhd ℂ (finiteEulerFactor χ S)
      {s : ℂ | σ < s.re} := by sorry
