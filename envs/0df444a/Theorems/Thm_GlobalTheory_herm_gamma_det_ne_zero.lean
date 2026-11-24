-- Prove2me | Theorems.Thm_GlobalTheory_herm_gamma_det_ne_zero
-- name    : GlobalTheory.herm_gamma_det_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:07.833288+00:00
-- url     : https://prove2.me/theorems/8f311ccf-1f58-4e96-89f9-f5b11ba179f0
-- title:
--   Global Theory: herm gamma det ne zero
-- statement:
--   The Global Theory construction uses the herm gamma det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianForms.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianForms.lean#L15-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfAdjointEndoRelatingHermitianForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.herm_gamma_det_ne_zero {g : ℕ} (H₁ : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) : H₁.det ≠ 0 := by sorry
