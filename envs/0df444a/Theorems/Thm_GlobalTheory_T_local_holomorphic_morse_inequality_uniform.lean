-- Prove2me | Theorems.Thm_GlobalTheory_T_local_holomorphic_morse_inequality_uniform
-- name    : GlobalTheory.T.local_holomorphic_morse_inequality_uniform
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:49.735656+00:00
-- url     : https://prove2.me/theorems/0fab8567-e804-5401-b3dc-2e1b47d80e9c
-- title:
--   T: local holomorphic morse inequality uniform
-- statement:
--   The T construction uses the local holomorphic morse inequality uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalHolomorphicMorseInequalityUniformStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalHolomorphicMorseInequalityUniformStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalHolomorphicMorseInequalityUniform
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalHolomorphicMorseInequalityUniformStatement
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.local_holomorphic_morse_inequality_uniform : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U → (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧ ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U → ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤ ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by sorry
