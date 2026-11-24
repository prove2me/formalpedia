-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_isUnipU_of_radQ
-- name    : GlobalTheory.CompanionTheory.InertTrans.isUnipU_of_radQ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:12.230751+00:00
-- url     : https://prove2.me/theorems/7cc85ee0-5808-4171-b447-c638b76a4382
-- title:
--   Inert Trans: is Unip U of rad Q
-- statement:
--   The Inert Trans construction uses the is Unip U of rad Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L45-L49

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

theorem GlobalTheory.CompanionTheory.InertTrans.isUnipU_of_radQ {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : IsUnipU u := by sorry
