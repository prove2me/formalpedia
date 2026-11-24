-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertGenFun_hasSum_counts
-- name    : GlobalTheory.CompanionTheory.InertGenFun.hasSum_counts
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:01:36.396017+00:00
-- url     : https://prove2.me/theorems/9b3986d0-6b1d-4909-97d0-c4d68a482365
-- title:
--   Inert Gen Fun: has Sum counts
-- statement:
--   The Inert Gen Fun construction uses the has Sum counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/GeneratingFunctionIdentity.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/GeneratingFunctionIdentity.lean#L8-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_GeneratingFunctionIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertGenFun

theorem GlobalTheory.CompanionTheory.InertGenFun.hasSum_counts (q N c : ℕ) (X : ℂ) (h : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j)
      (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)) := by sorry
