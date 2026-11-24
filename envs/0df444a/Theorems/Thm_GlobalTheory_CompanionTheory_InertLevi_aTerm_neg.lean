-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_aTerm_neg
-- name    : GlobalTheory.CompanionTheory.InertLevi.aTerm_neg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:10.733803+00:00
-- url     : https://prove2.me/theorems/2c93a79e-ef5b-4420-971a-be00ea797374
-- title:
--   Inert Levi: a Term neg
-- statement:
--   The Inert Levi construction uses the a Term neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/RecursionIdentity.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/RecursionIdentity.lean#L28-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi

theorem GlobalTheory.CompanionTheory.InertLevi.aTerm_neg {q N : ℕ} {X α : ℂ} (k : ℕ) :
    aTerm q N X α (-((k : ℤ) + 1)) = ((q : ℂ) ^ (N + 1) * X / α) * ((q : ℂ) ^ (N + 1) * X / α) ^ k := by sorry
