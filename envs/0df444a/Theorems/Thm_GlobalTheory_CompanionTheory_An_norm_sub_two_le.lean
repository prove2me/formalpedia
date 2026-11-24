-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_An_norm_sub_two_le
-- name    : GlobalTheory.CompanionTheory.An.norm_sub_two_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:18:51.402801+00:00
-- url     : https://prove2.me/theorems/d46afc5c-773b-4d73-918d-38f90064308c
-- title:
--   An: norm sub two le
-- statement:
--   The An construction uses the norm sub two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/OneLeNormOneSub.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/OneLeNormOneSub.lean#L30-L39

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

theorem GlobalTheory.CompanionTheory.An.norm_sub_two_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {w : ℂ}
    (hw : w ∈ zerosIn χ 0 1) : ‖w - 2‖ ≤ 7 / 2 := by sorry
