-- Prove2me | Theorems.Thm_GlobalTheory_herm_gamma_star_map_mulVec
-- name    : GlobalTheory.herm_gamma_star_map_mulVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:07.912557+00:00
-- url     : https://prove2.me/theorems/d035176f-05e0-414e-b5d8-d8d14a06c543
-- title:
--   Global Theory: herm gamma star map mul Vec
-- statement:
--   The Global Theory construction uses the herm gamma star map mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianForms.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfAdjointEndoRelatingHermitianForms.lean#L6-L9

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

theorem GlobalTheory.herm_gamma_star_map_mulVec {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) :
    star (M.map star *ᵥ v) = M *ᵥ star v := by sorry
