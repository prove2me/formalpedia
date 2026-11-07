-- Prove2me | Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_compact_weight_bound_principal_right
-- name    : OAI.CompactMellinBridge.pair_zero_free_of_compact_weight_bound_principal_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:18:17.892903+00:00
-- url     : https://prove2.me/theorems/85d600dc-5aef-414b-a3a4-f3565514600f
-- title:
--   Compact Mellin Bridge: pair zero free of compact weight bound principal right
-- statement:
--   The Compact Mellin Bridge construction uses the pair zero free of compact weight bound principal right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L551-L591
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L551-L591

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
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
open OAI.CompactMellinBridge

theorem OAI.CompactMellinBridge.pair_zero_free_of_compact_weight_bound_principal_right
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ
          (1 : DirichletCharacter ℂ r) n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧
      (1 : DirichletCharacter ℂ r).LFunction ρ ≠ 0 := by sorry
