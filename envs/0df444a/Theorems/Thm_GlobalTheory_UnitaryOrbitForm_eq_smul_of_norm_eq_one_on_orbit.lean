-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryOrbitForm_eq_smul_of_norm_eq_one_on_orbit
-- name    : GlobalTheory.UnitaryOrbitForm.eq_smul_of_norm_eq_one_on_orbit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:39.962731+00:00
-- url     : https://prove2.me/theorems/1bd4de8b-3e53-4a9e-b419-3e2b1fb8b414
-- title:
--   Unitary Orbit Form: eq smul of norm eq one on orbit
-- statement:
--   The Unitary Orbit Form construction uses the eq smul of norm eq one on orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L117-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L117-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}

theorem GlobalTheory.UnitaryOrbitForm.eq_smul_of_norm_eq_one_on_orbit :
    ∀ (r : ℕ) (A B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ), A.IsHermitian → B.IsHermitian →
      B.det ≠ 0 → (∀ h : Matrix (Fin r) (Fin r) ℂ, hᵀ * B * h.map (starRingEnd ℂ) = B →
        ‖(h *ᵥ v) ⬝ᵥ (A *ᵥ star (h *ᵥ v))‖ = 1) → ∃ t : ℝ, t ≠ 0 ∧ A = (t : ℂ) • B := by sorry
