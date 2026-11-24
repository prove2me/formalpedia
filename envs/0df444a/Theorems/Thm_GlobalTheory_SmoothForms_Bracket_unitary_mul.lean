-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Bracket_unitary_mul
-- name    : GlobalTheory.SmoothForms.Bracket.unitary_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:44.598801+00:00
-- url     : https://prove2.me/theorems/9b35937a-c82f-456b-aa4d-37ddbc41ea7a
-- title:
--   Bracket: unitary mul
-- statement:
--   The Bracket construction uses the unitary mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L35-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket
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
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Bracket
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
omit [FiniteDimensional ℝ 𝔸]

theorem GlobalTheory.SmoothForms.Bracket.unitary_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) :
    σ (a * b) * (a * b) = 1 := by sorry
