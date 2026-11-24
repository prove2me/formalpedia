-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_aTerm_nat
-- name    : GlobalTheory.CompanionTheory.InertLevi.aTerm_nat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:04:11.024179+00:00
-- url     : https://prove2.me/theorems/6a19bbef-bded-4d73-8087-98851be6ee2f
-- title:
--   Inert Levi: a Term nat
-- statement:
--   The Inert Levi construction uses the a Term nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/RecursionIdentity.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/RecursionIdentity.lean#L13-L26

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

theorem GlobalTheory.CompanionTheory.InertLevi.aTerm_nat {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (k : ℕ) :
    aTerm q N X α (k : ℤ) = ((q : ℂ) ^ (N + 1) * X * α) ^ k := by sorry
