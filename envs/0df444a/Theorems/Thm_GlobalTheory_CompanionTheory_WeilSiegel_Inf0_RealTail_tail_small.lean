-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_tail_small
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:23:30.182463+00:00
-- url     : https://prove2.me/theorems/a4ac232e-072f-4cc6-a7ba-318e95664705
-- title:
--   Real Tail: tail small
-- statement:
--   The Real Tail construction uses the tail small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L158-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L158-L275

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small : ∀ (P ι : Type) [Fintype P] [Fintype ι] (a : ℕ), 0 < a →
    ∀ (Q : (P → ι → ℝ) → (P → ℝ)), Measurable Q → ∀ C : ℝ≥0,
    (∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U) →
    ∀ f : (P → ι → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
    (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') →
    ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (P → ℝ), MeasurableSet U →
      ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by sorry
