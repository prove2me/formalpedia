-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_hasSum_aTerm
-- name    : GlobalTheory.CompanionTheory.InertLevi.hasSum_aTerm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:03:36.682096+00:00
-- url     : https://prove2.me/theorems/e0b498fc-8f6f-41e5-9892-f7d318c94ad8
-- title:
--   Inert Levi: has Sum a Term
-- statement:
--   The Inert Levi construction uses the has Sum a Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/RecursionIdentity.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/RecursionIdentity.lean#L44-L52

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

theorem GlobalTheory.CompanionTheory.InertLevi.hasSum_aTerm {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (h1 : ‖(q : ℂ) ^ (N + 1) * X * α‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X / α‖ < 1) :
    HasSum (aTerm q N X α) ((1 - (q : ℂ) ^ (N + 1) * X * α)⁻¹ +
      ((q : ℂ) ^ (N + 1) * X / α) * (1 - (q : ℂ) ^ (N + 1) * X / α)⁻¹) := by sorry
