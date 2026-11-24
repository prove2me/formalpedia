-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Bracket_der_eq
-- name    : GlobalTheory.SmoothForms.Bracket.der_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:35.248468+00:00
-- url     : https://prove2.me/theorems/2ef53375-6af4-40a6-aa36-c918b230becc
-- title:
--   Bracket: der eq
-- statement:
--   The Bracket construction uses the der eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L43-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L43-L68

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

theorem GlobalTheory.SmoothForms.Bracket.der_eq (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ} {a : 𝔸} (ha : σ a * a = 1)
    (hF : DifferentiableAt ℝ F a) (he : ∀ᶠ h in 𝓝 a, σ h * h = 1 → φ (g * s h) = F h) (Y : L) :
    Der (expMap j s) Y φ (g * s a) = fderiv ℝ F a (a * j Y) := by sorry
