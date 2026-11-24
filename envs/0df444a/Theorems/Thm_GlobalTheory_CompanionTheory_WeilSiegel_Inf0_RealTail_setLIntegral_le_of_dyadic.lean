-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_setLIntegral_le_of_dyadic
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.setLIntegral_le_of_dyadic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:23:10.293248+00:00
-- url     : https://prove2.me/theorems/5cc103ed-8256-4a3e-b333-2b12cf817173
-- title:
--   Real Tail: set LIntegral le of dyadic
-- statement:
--   The Real Tail construction uses the set LIntegral le of dyadic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L56-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L56-L96

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

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.setLIntegral_le_of_dyadic (f : (P → ι → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (M : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (T : Set (P → ι → ℝ)) (hT : MeasurableSet T)
    (hTK : ∀ x ∈ T, f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) ≤ K) (B : ℝ≥0∞)
    (hB : ∀ j : ℕ, volume (T ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      B * ENNReal.ofReal (((2 : ℝ) ^ j) ^ M)) :
    ∫⁻ x in T, ENNReal.ofReal (f x) ≤ ENNReal.ofReal (2 * K * 2 ^ (M + 1)) * B := by sorry
