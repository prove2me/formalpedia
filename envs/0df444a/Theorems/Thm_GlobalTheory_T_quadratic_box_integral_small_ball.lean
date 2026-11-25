-- Prove2me | Theorems.Thm_GlobalTheory_T_quadratic_box_integral_small_ball
-- name    : GlobalTheory.T.quadratic_box_integral_small_ball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:59.022066+00:00
-- url     : https://prove2.me/theorems/eba75d7e-d6d2-4fa4-b88b-786823205166
-- title:
--   T: quadratic box integral small ball
-- statement:
--   The T construction uses the quadratic box integral small ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBallStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBallStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBallStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quadratic_box_integral_small_ball : ∀ (P ι : Type) [Fintype P] [Fintype ι] (a : ℕ), 0 < a → ∀ (Q : (P → ι → ℝ) → (P → ℝ)), Measurable Q → ∀ C : ℝ≥0, (∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U) → ∀ f : (P → ι → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by sorry
