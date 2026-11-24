-- Prove2me | Theorems.Thm_GlobalTheory_morse_local
-- name    : GlobalTheory.morse_local
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:15.426174+00:00
-- url     : https://prove2.me/theorems/2090e90f-1264-489e-bcd3-020e69f026c3
-- title:
--   Global Theory: morse local
-- statement:
--   The Global Theory construction uses the morse local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalHolomorphicMorseInequalityUniform.lean#L28-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalHolomorphicMorseInequalityUniform.lean#L28-L242

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulIntegralBallLeOfCircleInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianPosSemidefOfLeviFormNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalHolomorphicMorseInequalityUniform
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
open GlobalTheory

theorem GlobalTheory.morse_local : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K →
    K ⊆ U → ContDiffOn ℝ 2 φ U →
    (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U →
    (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧
    ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U →
      ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤
        ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n *
          ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by sorry
