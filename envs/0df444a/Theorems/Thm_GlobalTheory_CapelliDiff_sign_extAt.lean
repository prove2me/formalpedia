-- Prove2me | Theorems.Thm_GlobalTheory_CapelliDiff_sign_extAt
-- name    : GlobalTheory.CapelliDiff.sign_extAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:04.320792+00:00
-- url     : https://prove2.me/theorems/e78f4616-f837-4d4f-99c0-7185cafc0429
-- title:
--   Capelli Diff: sign ext At
-- statement:
--   The Capelli Diff construction uses the sign ext At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QdetAddOneSubEqSumQminor.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QdetAddOneSubEqSumQminor.lean#L54-L57

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetAddOneSubEqSumQminor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory GlobalTheory.CapelliDiff

theorem GlobalTheory.CapelliDiff.sign_extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extAt k τ) = Equiv.Perm.sign τ := by sorry
