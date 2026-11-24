-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_An_one_le_norm_one_sub
-- name    : GlobalTheory.CompanionTheory.An.one_le_norm_one_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:18:42.926672+00:00
-- url     : https://prove2.me/theorems/8f9e0c4d-394d-4ad3-a952-047a945ef1c9
-- title:
--   An: one le norm one sub
-- statement:
--   The An construction uses the one le norm one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/OneLeNormOneSub.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/OneLeNormOneSub.lean#L11-L28

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__LogDerOne_a1ce1da79bfc3842
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_OneLeNormOneSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.An
open GlobalTheory.Mem.An

theorem GlobalTheory.CompanionTheory.An.one_le_norm_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h1 : χ ≠ 1) {w : ℂ}
    (hw : LFunction χ w = 0) (hB : w ∉ zerosIn χ 0 1) : 1 ≤ ‖1 - w‖ := by sorry
