-- Prove2me | Theorems.Thm_GlobalTheory_HermGram_reForm_apply
-- name    : GlobalTheory.HermGram.reForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:56.634161+00:00
-- url     : https://prove2.me/theorems/feb05df7-e059-4acd-8d19-9bfa9b057535
-- title:
--   Herm Gram: re Form apply
-- statement:
--   The Herm Gram construction uses the re Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.HermGram

theorem GlobalTheory.HermGram.reForm_apply {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    reForm H z w = (z ⬝ᵥ H *ᵥ star w).re := by sorry
