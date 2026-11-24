-- Prove2me | Theorems.Thm_GlobalTheory_T_rightDerivativeAlongLie_commutator_eq_bracket
-- name    : GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:56:34.888008+00:00
-- url     : https://prove2.me/theorems/79723fc5-66f6-4095-ba9f-12efb0e2e0e8
-- title:
--   T: right Derivative Along Lie commutator eq bracket
-- statement:
--   The T construction uses the right Derivative Along Lie commutator eq bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracketStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracketStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracketStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → ∀ X Y Z : L, j Z = j X * j Y - j Y * j X → Der (expMap j s) X (Der (expMap j s) Y φ) - Der (expMap j s) Y (Der (expMap j s) X φ) = Der (expMap j s) Z φ := by sorry
