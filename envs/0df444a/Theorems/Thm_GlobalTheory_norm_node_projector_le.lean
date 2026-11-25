-- Prove2me | Theorems.Thm_GlobalTheory_norm_node_projector_le
-- name    : GlobalTheory.norm_node_projector_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:04.988542+00:00
-- url     : https://prove2.me/theorems/aabf2563-498b-586a-948e-ddbe1784c514
-- title:
--   Global Theory: norm node projector le
-- statement:
--   The Global Theory construction uses the norm node projector le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NormEigenLePowMulNormSum.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NormEigenLePowMulNormSum.lean#L38-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormEigenLePowMulNormSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.norm_node_projector_le :
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (Nd : Finset κ) (s : κ) (Bd Cn : ℝ), s ∈ Nd → 0 ≤ Bd → (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) → (∀ x ∈ VV, T x ∈ VV) → (∀ j ∈ Nd.erase s, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ Nd.erase s, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) → (∀ x ∈ VV, ‖∑ i ∈ Nd, p i x‖ ≤ Cn * ‖x‖) → ∀ x ∈ VV, ‖p s x‖ ≤ Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by sorry
