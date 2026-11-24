-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_blk_mono
-- name    : GlobalTheory.CompanionTheory.InertTrans.blk_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:09.405083+00:00
-- url     : https://prove2.me/theorems/e092ee10-c7eb-442c-b82c-546ec9641cb4
-- title:
--   Inert Trans: blk mono
-- statement:
--   The Inert Trans construction uses the blk mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L33-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertTrans.blk_mono {i j : Fin (N + 2)} (h : j < i) : blk N j ≤ blk N i := by sorry
