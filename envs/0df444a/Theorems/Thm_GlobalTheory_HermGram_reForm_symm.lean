-- Prove2me | Theorems.Thm_GlobalTheory_HermGram_reForm_symm
-- name    : GlobalTheory.HermGram.reForm_symm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:30.933632+00:00
-- url     : https://prove2.me/theorems/49a25dd0-bbd6-4790-9df7-fe8c8c721b46
-- title:
--   Herm Gram: re Form symm
-- statement:
--   The Herm Gram construction uses the re Form symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L20-L29

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

theorem GlobalTheory.HermGram.reForm_symm {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (z w : Fin g → ℂ) : reForm H z w = reForm H w z := by sorry
