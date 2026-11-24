-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Bracket_der_der_eq
-- name    : GlobalTheory.SmoothForms.Bracket.der_der_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:16.972449+00:00
-- url     : https://prove2.me/theorems/84ea2e0d-d1f4-4a84-a850-200a2fcc0e31
-- title:
--   Bracket: der der eq
-- statement:
--   The Bracket construction uses the der der eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L70-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L70-L99

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

theorem GlobalTheory.SmoothForms.Bracket.der_der_eq (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ}
    (hF : ContDiffAt ℝ 2 F 1) (he : ∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → φ (g * s h) = F h) (X Y : L) :
    Der (expMap j s) X (Der (expMap j s) Y φ) g =
      fderiv ℝ (fderiv ℝ F) 1 (j X) (j Y) + fderiv ℝ F 1 (j X * j Y) := by sorry
