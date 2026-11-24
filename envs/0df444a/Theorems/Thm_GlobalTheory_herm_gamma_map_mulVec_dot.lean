-- Prove2me | Theorems.Thm_GlobalTheory_herm_gamma_map_mulVec_dot
-- name    : GlobalTheory.herm_gamma_map_mulVec_dot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:13.671964+00:00
-- url     : https://prove2.me/theorems/a87a3f15-c31b-4cc3-8f5e-d2629ee3f5ae
-- title:
--   Global Theory: herm gamma map mul Vec dot
-- statement:
--   The Global Theory construction uses the herm gamma map mul Vec dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianForms.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianForms.lean#L11-L13

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

theorem GlobalTheory.herm_gamma_map_mulVec_dot {g : ℕ} (B : Matrix (Fin g) (Fin g) ℂ) (z u : Fin g → ℂ) :
    (B *ᵥ z) ⬝ᵥ u = z ⬝ᵥ (Bᵀ *ᵥ u) := by sorry
