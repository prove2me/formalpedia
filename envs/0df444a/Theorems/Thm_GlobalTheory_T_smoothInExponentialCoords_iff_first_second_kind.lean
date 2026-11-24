-- Prove2me | Theorems.Thm_GlobalTheory_T_smoothInExponentialCoords_iff_first_second_kind
-- name    : GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:57:52.425869+00:00
-- url     : https://prove2.me/theorems/651383b2-471a-4c1c-9b81-18e5cb531bf1
-- title:
--   T: smooth In Exponential Coords iff first second kind
-- statement:
--   The T construction uses the smooth In Exponential Coords iff first second kind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKindStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKindStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKindStatement
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

theorem GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ T : Set L, Submodule.span ℝ T = ⊤ → ∀ φ : G → ℂ, Sm (expMap j s) φ ↔ ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => expMap j s (t i • Y i)).prod) := by sorry
